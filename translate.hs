{-# LANGUAGE
  ScopedTypeVariables
  #-}
module Translate where

import Prelude hiding (catch)
import Test.HUnit hiding (assert)
import List ((\\))
import Monad
import Control.Exception hiding (assert)
import Foreign (unsafePerformIO)

import ListKit
import FPKit
import Basics
import NRC
import SQL
import NRCPretty
import Debug
import Embed

-- { Compilation } --

-- | Normalize db terms on a CBV evaluation strategy
-- List of strings is an environment: the variables it is ok not to normalize
normTerm :: [(String,QType)] -> TypedTerm -> TypedTerm
normTerm env (m@(Unit, _)) = m
normTerm env (DB m, _) = normTerm env m
normTerm env (m@(Bool b, _)) = m
normTerm env (m@(Num n, _)) = m
normTerm env (PrimApp fun args, t) = (PrimApp fun (map (normTerm env) args), t)
normTerm env (Var x, t) = 
    if x `maps` env then (Var x, t) else
      error $ "Free variable "++ x ++ " in normTerm"
normTerm env (Abs x n, t) = (Abs x n, t)
normTerm env (App l m, t) = 
    let w = normTerm env m in
    case normTerm env l of 
      (Abs x n, _) -> 
          unsafePerformIO $
          catch (evaluate$
            let !n' = substTerm x w n in
            normTerm env (snd $ runTyCheck env $ n')
          ) (\(exc::SomeException) ->
            breakFlag $ 
            debug ("susbtituting "++show w++" for "++x++" in "++show n) $
             Control.Exception.throwIO exc
          )
      (If b l1 l2, _) ->
          (normTerm env (If b (App l1 w, t) (App l2 w, t), t))
      v -> error $ "unexpected normal form in appl posn in normTerm" ++ show v
normTerm env (Table s t, t') = (Table s t, t')
normTerm env (If b m (Nil, _), t@(TList _, _)) =
    let b' = normTerm env b in
    case normTerm env m of
      (Nil, _) -> (Nil, t)
      (Singleton m', _) -> (If b' (Singleton m', t) (Nil, t), t)
      (Table s fTys, _) -> (If b' (Table s fTys, t) (Nil, t), t)
      (Comp x l m', _) -> normTerm env (Comp x l (If b' m' (Nil, t), t), t)
      (m1 `Union` m2, _) -> ((normTerm env (If b' m1 (Nil, t), t)) `Union`
                             (normTerm env (If b' m2 (Nil, t), t)), t)
      m@(If _ _ _, _) -> (If b' m (Nil, t), t)
      v -> error $ "unexpected normal form in conditional body in normTerm: " ++
                    show v
normTerm env (If b@(_,bTy) m n, t@(TList _, _)) = -- n /= Nil
    ((normTerm env (If b m (Nil, t), t)) `Union` 
     (normTerm env (If (PrimApp "not" [b], bTy) m (Nil, t), t)), t)
normTerm env (If b m n, t@(TRecord fTys, eff)) =
    let b' = normTerm env b in
    let (Record mFields, _) = normTerm env m
        (Record nFields, _) = normTerm env n in
    (Record[(l, (If b' (image l mFields) (image l nFields), (image l fTys,eff)))
            | (l, _) <- mFields],
     t)
normTerm env (If b m n, t) = 
    (If (normTerm env b) (normTerm env m) (normTerm env n), t)
normTerm env (Singleton m, t) = (Singleton (normTerm env m), t)
normTerm env (Nil, t) = (Nil, t)
normTerm env (m `Union` n, t) = ((normTerm env m) `Union` (normTerm env n), t)
normTerm env (Record fields, t) =
    (Record [(a, normTerm env m) | (a, m) <- fields], t)
normTerm env (Project m a, t) = 
    case normTerm env m of
      (Record fields, _) -> case (lookup a fields) of 
                              Just x -> x ; Nothing -> error$"no field " ++ a
      -- ah, the following not necessary because if pushes into records.
      (If b m' n',_)-> normTerm env (If b (Project m' a, t) (Project n' a, t), t)
      (m@(Var x, t)) -> (Project m a, t)
      v -> error $ "Unexpected normal form in body of Project in normTerm: " ++ 
                    show v
normTerm env (Comp x m n, t) =
    let insert k ((v,t) :: TypedTerm) =
            case v of
              Nil -> (Nil, t)
              n1 `Union` n2 -> ((insert k n1) `Union` (insert k n2), t)
              _ -> k (v,t)
        insertFurther k ((v,t) :: TypedTerm) =
            case v of
              Nil -> (Nil, t)
              n1 `Union` n2 -> 
                  ((insertFurther k n1) `Union` (insertFurther k n2), t)
              Comp x m n -> (Comp x m (insertFurther k n), t)
              _ -> k (v,t)
    in case normTerm env m of
      (Nil, _) -> (Nil, t)
      (Singleton m', _) -> 
          unsafePerformIO $
          catch (evaluate$
            let !n' = substTerm x m' n in
            normTerm env (snd $ runTyCheck env $ n')
          ) (\(exc::SomeException) ->
            breakFlag $
            debug ("susbtituting "++show m'++" for "++x++" in "++show n) $ 
             Control.Exception.throwIO exc
          )
      (Comp y l' m', s) ->
          let (y', n') = if y `elem` fvs n then
                             let y' = head $ variables \\ fvs n in
                             (y', rename y y' n)
                         else (y, n) 
          in
            (normTerm env (Comp y' l' (Comp x m' n', t), t))
      (m1 `Union` m2, _) ->
          ((normTerm env (Comp x m1 n, t)) `Union` 
           (normTerm env (Comp x m2 n, t)), t)
      (tbl @ (Table s fTys, _)) ->
          insert (\(v,t) -> (Comp x tbl (v,t), t)) $
                 normTerm ((x,([],TList(TRecord fTys))):env) n
      (If b m' (Nil, _), _) ->
          assert (x `notElem` fvs b) $
          let v = (normTerm env (Comp x m' n, t)) in
          insertFurther (\(v,t) -> (If b (v,t) (Nil, t), t)) v
--           insert  (\(v,t) -> (Comp x m' (v,t), t)) $
--             insertFurther (\(v,t) -> (If b (v,t) (Nil, t), t)) (normTerm env n)
      v -> error$ "unexpected normal form in source of comprehension: " ++ show v
normTerm env (z@(Do _ _), _) = 
    error ("unexpected side-effect action in normalization: " ++ pretty z)

make_test_normalizer = 
    do initialTyEnv <- makeInitialTyEnv 
       return$ TestList 
                 [TestCase $ unitAssert $ 
                  let term = (Comp "x" (Table "foo" [("fop", TNum)], ())
                              (If (Bool True,())
                               (Singleton (Record
                                           [("f0", (Project (Var "x", ())
                                                    "fop",()))],()),())
                               (Singleton (Record 
                                           [("f0", (Num 3, ()))], ()), ()), 
                               ()), ()) in
                  let tyTerm = runErrorGensym $ infer $ term in
                  groundQuery $ compileTerm $ normTerm initialTyEnv $ tyTerm
                 ]

utests = do make_test_normalizer <- make_test_normalizer 
            return $ TestList [tyCheckTests, make_test_normalizer, test_typing]

unitTest = runErrorGensym $ liftM runTestTT utests

-- | @compileTerm@ compositionally translates a normal-form @Term@ to a @Query@.
compileTerm :: TypedTerm -> Query
compileTerm (v `Union` u, _)       = (compileTerm v) `QUnion` (compileTerm u)
compileTerm (Nil, _)               = Select {rslt=[],tabs=[],cond=[QBool False]}
compileTerm (f@(Comp x (Table tabname fTys, _) n, _))               = compileF f
compileTerm (f@(If b z (Nil, _), _))                                = compileF f
compileTerm (f@(Singleton (Record fields, _), _))                   = compileF f
compileTerm (f@(Table tabname fTys, _))                             = compileF f
compileTerm x =    error $ "compileTerm got unexpected term: " ++ (pretty.fst) x

compileF (Comp x (Table tabname fTys, _) n, _)                      =
    let q@(Select _ _ _) = compileF n in
    Select {rslt=rslt q,
            tabs = (Imm tabname, x, TRecord fTys):tabs q,
            cond = cond q}
compileF (z@(If _ _ (Nil, _), _))                                   = compileZ z
compileF (z@(Singleton (Record fields, _), _))                      = compileZ z
compileF (z@(Table tabname fTys, _))                                = compileZ z
compileF (z, _) = error ("compileF got unexpected term: " ++ pretty z)

compileZ (If b z (Nil, _), _) =
    let q@(Select _ _ _) = compileZ z in
    Select {rslt=rslt q, tabs = tabs q, cond = compileB b : cond q}
compileZ (Singleton (Record fields, _), _) = 
    Select {rslt = (alistmap compileB fields), tabs = [], cond = []}
compileZ (Table tabname fTys, _) =
    Select {rslt = [(l,QField tabname l)| (l,ty) <- fTys],
            tabs = [(Imm tabname, tabname, TRecord fTys)], cond = []}
compileZ z = error$ "compileZ got unexpected term: " ++ (pretty.fst) z

compileB (If b b' b'', _)        = QIf (compileB b) (compileB b') (compileB b'')
compileB (Bool n, _)                 = QBool n
compileB (Num n, _)                  = QNum n
compileB (Project (Var x, _) l, _)   = QField x l
compileB (PrimApp "not" [arg], _)    = QNot (compileB arg)
compileB b = error$ "compileB got unexpected term: " ++ (pretty.fst) b

-- | addRslt: Add a named result column to a query.
addRslt :: (Field, Query) -> Query -> Query
addRslt r q = q {rslt = r : rslt q}

-- | crossTab: cross product of two tables
crossTab :: (TableExpr, String, Type) -> Query -> Query
crossTab (t, alias, ty) q = 
    q {tabs = tabs q ++ [(t, alias, ty)]}

-- | filterQ: add a filtering condition (the 1st param) to the query in
-- the 2nd param.
filterQ :: Query -> Query -> Query
filterQ condn q =
    q {cond = condn : cond q}

theOneQ = (Select {rslt=[("_id", QNum 1)], tabs=[], cond=[]})

theRowNumQ = (Select {rslt=[("_id", QRownum)], tabs=[], cond=[]})

-- | compileNestedTerm translates a normal-form Term of nested type to a
-- list of Querys using the (NAME?) encoding.
compileNested :: TypedTerm -> [(String, Query)]
compileNested v =
    let (q, qEtc) = compileNestedTerm theRowNumQ [] "main" v in
    ("main",q):qEtc

compileNestedTerm :: Query -> [(Var, Field)] -> String -> TypedTerm
                  -> (Query, [(String, Query)])
compileNestedTerm parent parentFieldNames name v =
    let (q, qEtc) = (compileNestedTermAux parent parentFieldNames name v) in
    (q {rslt = ("_id", QRownum) : rslt q}, qEtc)

compileNestedTermAux :: Query -> [(Var, Field)] -> String -> TypedTerm
                     -> (Query, [(String,Query)])
compileNestedTermAux parent parentFieldNames name (v `Union` u, _) = 
    let (v', vEtc) = (compileNestedTermAux parent parentFieldNames name v) in
    let (u', uEtc) = (compileNestedTermAux parent parentFieldNames name u) in
    (v' `QUnion` u', vEtc ++ uEtc)
compileNestedTermAux parent parentFieldNames name (Nil, _) =
    (Select {rslt=[],tabs=[],cond=[QBool False]}, [])
compileNestedTermAux parent parentFieldNames name (f@(Comp x (Table tabname fTys, _) n, _))
    = compileNestedF parent parentFieldNames name f
compileNestedTermAux parent parentFieldNames name (f@(If b z (Nil, _), _))
    = compileNestedF parent parentFieldNames name f
compileNestedTermAux parent parentFieldNames name (f@(Singleton (Record fields, _), _))
    = compileNestedF parent parentFieldNames name f
compileNestedTermAux parent parentFieldNames name (f@(Singleton v, _))
    = compileNestedF parent parentFieldNames name f
compileNestedTermAux parent parentFieldNames name (f@(Table tabname fTys, _))
    = compileNestedF parent parentFieldNames name f
compileNestedTermAux parent parentFieldNames name x =
    error $ "compileNestedTermAux got unexpected term: " ++ (pretty.fst) x

-- compileNestedFAux parent name v =
--     let q = compiledNestedF parent name v in
--     ("_id", QRownum) : rslt q

-- | Alias x.l as 'x_l' for each l in the names list.
encodedQualifiedNames x names = 
    [(x ++ "_" ++ nm, QField x nm) | nm <- names]

widen :: [(Field, Query)] -> Query -> Query
widen newFields q = q {rslt = rslt q ++ newFields}

compileNestedF :: Query -> [(Var, Field)] -> String -> TypedTerm
               -> (Query, [(String, Query)])
compileNestedF parent parentFieldNames schemaPathName (term@(Comp x (Table tabname fTys, _) body, _)) =
    let parent' = crossTab (Imm tabname, x, TRecord fTys) parent in
    let sourceNames = [nm | (nm, _) <- fTys] in
    let parent'' = widen (encodedQualifiedNames x sourceNames) parent' in
    let body' = body in
    let parentFieldNames' = [(x,nm) | (nm, _) <- fTys] ++ parentFieldNames in
    let (q@(Select _ _ _), qEtc) =
            compileNestedF parent'' parentFieldNames' schemaPathName body' in
    let q' = q {tabs = (Imm tabname, x, TRecord fTys):tabs q} in
    (q', qEtc)
compileNestedF parent parentFieldNames schemaPathName (z@(If _ _ (Nil, _), _))
    = compileNestedZ parent parentFieldNames schemaPathName z
compileNestedF parent parentFieldNames schemaPathName (z@(Singleton v, _))
    = compileNestedZ parent parentFieldNames schemaPathName z
compileNestedF parent parentFieldNames schemaPathName (z@(Table tabname fTys, _))
    = compileNestedZ parent parentFieldNames schemaPathName z
compileNestedF parent parentFieldNames schemaPathName (z, _)
    = error ("compileNestedF got unexpected term: " ++ pretty z)

compileNestedZ :: Query -> [(Var, Field)] -> String -> TypedTerm
               -> (Query, [(String, Query)])
compileNestedZ parent parentFieldNames schemaPathName (If b z (Nil, _), _) =
    let b' = compileNestedB b in
    let parent' = filterQ b' parent in
    let (q@(Select _ _ _), qEtc) = compileNestedZ parent' parentFieldNames schemaPathName z in
--    let q' = filterQ b' q in
    let q' = Select {rslt=rslt q, tabs = tabs q, cond = b' : cond q} in
    (q', qEtc)
compileNestedZ parent parentFieldNames schemaPathName (Singleton r, _) =
    compileNestedR parent parentFieldNames schemaPathName r
compileNestedZ parent parentFieldNames schemaPathName (Table tabname fTys, _) =
    (Select {rslt = [(l,QField tabname l)| (l,ty) <- fTys],
             tabs = [(Imm tabname, tabname, TRecord fTys)], cond = []},
     [])
compileNestedZ parent parentFieldNames schemaPathName (z, _) = 
    error $ "compileNestedZ got unexpected term: " ++ pretty z

compileNestedR :: Query -> [(Var, Field)] -> String -> TypedTerm
               -> (Query, [(String,Query)])
compileNestedR parent parentFieldNames schemaPathName (Record fields, _) =
    let (items, otherTables) =
            unzip [((nm, qExpr), etc)
                   | (nm, expr) <- fields,
                     let (qExpr, etc) = compileNestedItem parent parentFieldNames (schemaPathName ++ "_" ++ nm) expr
                  ] in
    (Select {rslt = items, tabs = [], cond = []}, concat otherTables)

-- FIXME: non-records as singleton contents may not fully work
compileNestedR parent parentFieldNames schemaPathName v =
    let fieldName = "_value" in
    let schemaPathName' = schemaPathName ++ "_" ++ fieldName in
    let (rslt, etc) = compileNestedItem parent parentFieldNames schemaPathName' v in
    (Select {rslt = [(fieldName, rslt)], tabs = [], cond = []}, etc)

parentifyNames names term =
    foldr (\(tbl,lbl) -> replace (tbl, lbl) ("_parent", tbl ++ "_" ++ lbl))
          term
          names

compileNestedItem :: Query -> [(Var, Field)] -> String -> TypedTerm
                  -> (Query, [(String,Query)])
compileNestedItem parent parentFieldNames schemaPathName (b@(If _ _ _, _))             = (compileNestedB b, []) -- FIXME: really needs to be type-directed
compileNestedItem parent parentFieldNames schemaPathName (b@(Bool _, _))               = (compileNestedB b, [])
compileNestedItem parent parentFieldNames schemaPathName (b@(Num _, _))                = (compileNestedB b, [])
compileNestedItem parent parentFieldNames schemaPathName (b@(Project (Var _, _) _, _)) = (compileNestedB b, [])
compileNestedItem parent parentFieldNames schemaPathName (b@(PrimApp _ _, _))          = (compileNestedB b, [])
compileNestedItem parent parentFieldNames schemaPathName v =
    let v' = parentifyNames parentFieldNames v in
    let (q, qEtc) = compileNestedTerm parent parentFieldNames schemaPathName v' in
    let q' = Select {rslt = (("_parent", QField "_parent" "_id") : rslt q),
                     tabs = tabs q ++ [(SubQuery parent, "_parent",
                                        TNum -- FIXME: the real type is a record
                                       )],
                     cond = cond q} in
    (QNum 0, (schemaPathName, q'):qEtc)

compileNestedB (If b b' b'', _)            = QIf (compileNestedB b)
                                                 (compileNestedB b')
                                                 (compileNestedB b'') 
compileNestedB (Bool n, _)                 = (QBool n)
compileNestedB (Num n, _)                  = (QNum n)
compileNestedB (Project (Var x, _) l, _)   = QField x l
compileNestedB (PrimApp "not" [arg], _)    = QNot (compileNestedB arg)
compileNestedB (PrimApp "=" [x,y], _)      = QOp (compileNestedB x) Eq
                                                 (compileNestedB y)
compileNestedB b = error $ "compileNestedB got unexpected term: " ++ (pretty.fst) b

{----------------------------------- Tests -----------------------------------}

typecheckCompilePretty term = 
      let qs = compileNested $ entagulate runInferEffects term in
      (alistmap pretty $ qs)

test_compileNested =
    TestList [
      typecheckCompilePretty
        (foreach "x" (table "bar" [("depth", TNum), ("width", TNum)])
         (having (primApp "=" [(project (var "x") "depth"), (Num 17, ())])
          (singleton (record
                      [("ys",
                        (foreach "y" (table "foo" [("height", TNum), ("name", TBool)])
                         (having (primApp "=" [(project (var "y") "height"), (project (var "x") "width")])
                          (singleton (record [("nomen", (project (var "y") "name"))]))
                         )))]))
          ))
      ~?=
      [("main",
        "select row_number() over () as _id, 0 as ys from bar as x where x.depth = 17"),
       ("main_ys",
        "select _parent._id as _parent, row_number() over () as _id, y.name as nomen " ++ 
        "from foo as y, (select row_number() over () as _id, x.depth as x_depth, x.width as x_width from bar as x where x.depth = 17) as _parent " ++
        "where y.height = _parent.x_width")
      ]
      ,
      typecheckCompilePretty
        (foreach "w" (table "baz" [("mass", TNum), ("charge", TNum)])
          (singleton (record [("q", 
             (foreach "x" (table "bar" [("depth", TNum), ("width", TNum)])
              (having (primApp "=" [(project (var "x") "depth"), (Num 17, ())])
               (singleton (record
                           [("ys",
                             (foreach "y" (table "foo" [("height", TNum), ("name", TBool)])
                              (having (primApp "=" [(project (var "y") "height"), (project (var "x") "width")])
                               (singleton (record [("nomen", (project (var "y") "name")),
                                                   ("verve", (project (var "w") "charge"))]))
                              )))]))
              ))
          )])))
      ~?=
      [("main",
        "select row_number() over () as _id, 0 as q from baz as w where true"),
       ("main_q",
        "select _parent._id as _parent, row_number() over () as _id, 0 as ys from bar as x, (select row_number() over () as _id, w.mass as w_mass, w.charge as w_charge from baz as w where true) as _parent where x.depth = 17"),
       ("main_q_ys",
        "select _parent._id as _parent, row_number() over () as _id, y.name as nomen, _parent.w_charge as verve " ++ 
        "from foo as y, (select row_number() over () as _id, w.mass as w_mass, w.charge as w_charge, x.depth as x_depth, x.width as x_width from baz as w, bar as x where x.depth = 17) as _parent " ++
        "where y.height = _parent.x_width")
      ]
    ]

-- TBD: HUnit should give me a way to inspect the results actually produced.
