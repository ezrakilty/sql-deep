{-# LANGUAGE ScopedTypeVariables #-}

module NRC where

-- import Monad hiding (when, join)
import Test.HUnit hiding (State, assert)
import Test.QuickCheck
import QCUtils
import Control.Monad.Error hiding (when, join)
import Control.Monad.State hiding (when, join)
import Maybe (fromMaybe)
import List (nub, (\\), sort, sortBy, groupBy, intersperse)

import Gensym
import ListKit
import NumKit
import FPKit
import Basics
import Debug

data Term' a = Unit | Bool Bool | Num Integer | PrimApp String [Term a]
             | Var Var | Abs Var (Term a) | App (Term a) (Term a)
             | Do Effect (Term a) | DB (Term a)
             | Table Tabname [(Field, Type)]
             | If (Term a) (Term a) (Term a)
             | Singleton (Term a) | Nil | Union (Term a) (Term a)
             | Record [(String, Term a)]
             | Project (Term a) String
             | Comp Var (Term a) (Term a)
--           | Empty (Term a)
    deriving (Eq,Show)

type Term a = (Term' a, a)
--    deriving (Eq,Show)

type RowSubst = [(Int, EffectRow)]

type TyEff = (Type, EffectRow)

type QType = ([TyVar], Type)

type TySubst = [(Int, Type)]

rowVar = snd
rowElems = fst

type TyEffSubst = (TySubst, RowSubst)


-- Operations on terms

fvs (Unit, _) = []
fvs (Bool _, _) = []
fvs (Num _, _) = []
fvs (PrimApp prim args, _) = union $ map fvs args
fvs (Var x, _) = [x]
fvs (Abs x n, _) = fvs n \\ [x]
fvs (App l m, _) = fvs l `u` fvs m
fvs (Do _ m, _) = fvs m
fvs (DB body, _) = fvs body
fvs (Table _ _, _) = []
fvs (If c a b, _) = fvs c `u` fvs a `u` fvs b
fvs (Nil, _) = []
fvs (Singleton elem, _) = fvs elem
fvs (Union m n, _) = fvs m `u` fvs n
fvs (Record fields, _) = union $ map (fvs . snd) fields
fvs (Project targ _, _) = fvs targ
fvs (Comp x src body, _) = fvs src `u` (fvs body \\ [x])

variables = map ('y':) $ map show [0..]

rename x y (Var z, q) | x == z    = (Var y, q)
                      | otherwise = (Var z, q)
rename x y (l@(Abs z n, q)) | x == z    = l
                            | otherwise = (Abs z (rename x y n), q)
rename x y (App l m, q) = (App (rename x y l) (rename x y m), q)
rename x y (PrimApp prim args, q) = (PrimApp prim (map (rename x y) args), q)
rename x y (Singleton elem, q) = (Singleton (rename x y elem), q)
rename x y (Project targ label, q) = (Project (rename x y targ) label, q)
rename x y (Record fields, q) = (Record (alistmap (rename x y) fields), q)
rename x y (DB body, q) = (DB (rename x y body), q)
rename x y (Comp z src body, q) 
    | x == z = (Comp z src body, q)
    | y == z = let y' = head $ variables \\ [y] in
               let body' = rename y y' body in
                 (Comp z (rename x y src) (rename x y body'), q)
    | otherwise= (Comp z (rename x y src) (rename x y body), q)
rename x y (Num n, q) = (Num n, q)
rename x y (Bool b, q) = (Bool b, q)
rename x y (Table s t, q) = (Table s t, q)
rename x y (If c a b, q) = (If (rename x y c) (rename x y a) (rename x y b), q)

--substTerm x v m: substite v for x in term m
-- (incorrect because it does not make substitutions in the q)
substTerm x v (m@(Unit, _))       = m
substTerm x v (m@(Bool b, _))     = m
substTerm x v (m@(Num n, _))      = m
substTerm x v (m@(Table s t, _))  = m
substTerm x v (m@(Nil, _))        = m
substTerm x v (Singleton elem, q) = (Singleton (substTerm x v elem), q)
substTerm x v (Union m n, q) = (Union (substTerm x v m) (substTerm x v n), q)
substTerm x v (m@(Var y, _)) | y == x    = v
                             | otherwise = m
substTerm x v (l @ (Abs y n, q))
    | x == y            = l
    | y `notElem` fvs v = (Abs y (substTerm x v n), q) 
    | otherwise = 
        let y' = head $ variables \\ fvs v in
        let n' = rename y y' n in
        (Abs y' (substTerm x v n'), q)
substTerm x v (Do e m, q) = (Do e (substTerm x v m), q)
substTerm x v (App l m, q) = (App (substTerm x v l) (substTerm x v m), q)
substTerm x v (PrimApp prim args,q)= (PrimApp prim (map (substTerm x v) args),q)
substTerm x v (Project targ label, q) = (Project (substTerm x v targ) label, q)
substTerm x v (Record fields, q) = (Record (alistmap (substTerm x v) fields), q)
substTerm x v (DB body, q) = (DB (substTerm x v body), q)
substTerm x v (Comp y src body, q) 
    | x == y    =
        (Comp y src' body, q)
    | y `notElem` fvs v =
        (Comp y src' (substTerm x v body), q)
    | otherwise = 
        let y' = head $ variables \\ fvs v in
        let body' = rename y y' body in
        (Comp y' src' (substTerm x v body'), q)
    where src' = (substTerm x v src)
substTerm x v (If c a b, q) = 
    (If (substTerm x v c) (substTerm x v a) (substTerm x v b), q)

-- | Replace occurrences of y.l with y'.l'
replace (y, l) (y', l') (term@(Project (Var x, t) l'', t'))
    | y == x && l == l''
        = debug "replacing!" $ (Project (Var y', t) l', t')
    | otherwise = term
replace (y, l) (y', l') (m@(Unit, _))       = m
replace (y, l) (y', l') (m@(Bool b, _))     = m
replace (y, l) (y', l') (m@(Num n, _))      = m
replace (y, l) (y', l') (m@(Table s t, _))  = m
replace (y, l) (y', l') (m@(Nil, _))        = m
replace (y, l) (y', l') (Singleton elem, q) = (Singleton (replace (y, l) (y', l') elem), q)
replace (y, l) (y', l') (Union m n, q) = (Union (replace (y, l) (y', l') m) (replace (y, l) (y', l') n), q)
replace (y, l) (y', l') (m@(Var x, _)) | y == x =
    error $ "raw occurrence of variable " ++ x ++
            " when replacing field " ++ y ++ "." ++ l ++
            " by " ++ y' ++ "." ++ l'
                                 | otherwise = m
replace (y, l) (y', l') (abs @ (Abs z n, q))
    | z == y            = abs
    | otherwise = 
        (Abs z (replace (y, l) (y', l') n), q)
replace (y, l) (y', l') (Do e m, q) = (Do e (replace (y, l) (y', l') m), q)
replace (y, lbl) (y', lbl') (App l m, q) = (App (replace (y, lbl) (y', lbl') l) (replace (y, lbl) (y', lbl') m), q)
replace (y, l) (y', l') (PrimApp prim args,q)= (PrimApp prim (map (replace (y, l) (y', l')) args),q)
replace (y, l) (y', l') (Project targ label, q) = (Project (replace (y, l) (y', l') targ) label, q)
replace (y, l) (y', l') (Record fields, q) = (Record (alistmap (replace (y, l) (y', l')) fields), q)
replace (y, l) (y', l') (DB body, q) = (DB (replace (y, l) (y', l') body), q)
replace (y, l) (y', l') (Comp z src body, q) 
    | y == z    =
        (Comp z src' body, q)
    | otherwise = 
        (Comp z src' (replace (y, l) (y', l') body), q)
    where src' = (replace (y, l) (y', l') src)
replace (y, l) (y', l') (If c a b, q) = 
    (If (replace (y, l) (y', l') c) (replace (y, l) (y', l') a) (replace (y, l) (y', l') b), q)

-- lazyDepth: calculate a list (poss. inf.) whose sum is the depth of the term.
lazyDepth :: Term a -> [Int]
lazyDepth (Abs _ n, _) = 1 : lazyDepth n
lazyDepth (App l m, _) = 1 : zipWith max (lazyDepth l) (lazyDepth m)
lazyDepth (Project m _, _) = 1 : lazyDepth m
lazyDepth (Singleton m, _) = 1 : lazyDepth m
lazyDepth (DB m, _) = 1 : lazyDepth m
lazyDepth (PrimApp prim args, _) =
    1 : foldr1 (zipWith max) (map lazyDepth args)
lazyDepth (Record fields, _) =
    1 : foldr1 (zipWith max) (map (lazyDepth . snd) fields)
lazyDepth (Comp _ src body, _) =
    1 : zipWith max (lazyDepth src) (lazyDepth body)
lazyDepth _ = 1 : []

-- Failure and ErrorGensym monad

type Failure = Either String

runError :: Either String t -> t
runError (Left e) = breakFlag $ error e
runError (Right x) = x

runErrorGensym = runError . runGensym . runErrorT

-- Operations on types, rows and substitutions

ftvs TBool = []
ftvs TNum = []
ftvs TUnit = []
ftvs (TList t) = ftvs t
ftvs (TArr s _ t) = ftvs s ++ ftvs t
ftvs (TRecord fields) = concat [ftvs t | (lbl, t) <- fields]
ftvs (TVar a) = [a]

ftvsSubst a = concatMap ftvs $ rng a

-- Row operations

newOpenEmptyRow :: ErrorT String Gensym ([a], Maybe Int)
newOpenEmptyRow = do rowVar <- lift gensym; return ([], Just rowVar)

unifyEffectRow :: EffectRow -> EffectRow -> Failure TyEffSubst
unifyEffectRow (effs1, Nothing) (effs2, Nothing) =
    if (effs1 `setEq` effs2) then return ([], []) else
        fail("Closed effect mismatch between " ++ show effs1 ++ 
             " and " ++ show effs2)
unifyEffectRow (effs1, Just rho1) (effs2, Nothing) =
    if effs2 `contains` effs1 then 
        return ([], [(rho1, (effs2 \\\ effs1, Nothing))])
    else fail("Closed row " ++ show (effs2, Nothing::Maybe Int) ++
               " lacks fields present in open row " ++ show (effs1, Just rho1))
unifyEffectRow (effs1, Nothing) (effs2, Just rho2) =
    if effs1 `contains` effs2 then 
        return ([], [(rho2, (effs1 \\\ effs2, Nothing))])
    else fail("Closed row " ++ show (effs1, Nothing::Maybe Int) ++
               " lacks fields present in open row " ++ show (effs2, Just rho2))
unifyEffectRow (a@(effs1, Just rho1)) (b@(effs2, Just rho2)) =
    -- Each row var maps to the effs present in the other, missing 
    --   from its own row.
    -- With fancy effects, would need to unify the matching ones.
    if rho1 == rho2 then if effs1 `bagEq` effs2 then return ([],[]) else 
                             fail$"circular row variable unifying "++show a++
                                     " and "++show b++""
    else
       return([], [(rho1, (effs2 \\\ effs1, Just rho1)),
                   (rho2, (effs1 \\\ effs2, Just rho1))])

applyRowSubst :: [(Int, EffectRow)] -> EffectRow -> EffectRow 
applyRowSubst env (elems, Nothing) = (elems, Nothing)
applyRowSubst env (elems, Just rowVar) =
    case lookup rowVar env of
      Nothing -> (elems, Just rowVar)
      Just (elems', rowVar') ->
          (nub $ elems ++ elems', rowVar')

composeRowSubst :: [RowSubst] -> RowSubst
composeRowSubst = 
    foldr (\s1 s2 ->
           (shadow s1 s2 ++                -- elements of s1 not shadowed by s2
            alistmap (applyRowSubst s1) s2 -- and s2, with s1 applied inside
           )) []

    -- Property: Row unification gives a substitution that 
    --   actually unifies the two rows.
prop_unify_apply_rowSubst = 
  forAll arbitrary $ \a ->
  forAll arbitrary $ \b -> 
    rowVar a /= rowVar b ==>
      either (const$ False ==> False) (property) $
      do subst <- unifyEffectRow a b
         let e = rowElems $ applyTyEffSubstEff subst a
         let f = rowElems $ applyTyEffSubstEff subst b
         return $ e `bagEq` f

occurs x (TVar y) | x == y    = True
                  | otherwise = False
occurs x (TArr s _ t) = x `occurs` s || x `occurs` t
occurs x (TList t) = x `occurs` t
occurs x (TRecord t) = any (occurs x) (map snd t)
occurs x (TUnit) = False
occurs x (TBool) = False
occurs x (TNum) = False

applyTySubst :: TySubst -> Type -> Type
applyTySubst subst (TUnit) = TUnit
applyTySubst subst (TBool) = TBool
applyTySubst subst (TNum) = TNum
applyTySubst subst (TVar a) = case lookup a subst of
                              Nothing -> TVar a
                              Just ty -> ty
applyTySubst subst (TArr a e b) =
    TArr (applyTySubst subst a) e (applyTySubst subst b)
applyTySubst subst (TList a) = TList (applyTySubst subst a)
applyTySubst subst (TRecord a) = TRecord (alistmap (applyTySubst subst) a)

-- applyEffSubstTy: given an effect-row substitution, apply it to all
-- the effects appearing on arrows in a given type.
applyEffSubstTy :: RowSubst -> Type -> Type
applyEffSubstTy _ TBool = TBool
applyEffSubstTy _ TNum = TNum
applyEffSubstTy _ TUnit = TUnit
applyEffSubstTy subst (TArr s e t) =
    TArr (applyEffSubstTy subst s) (applyRowSubst subst e)
         (applyEffSubstTy subst t)
applyEffSubstTy subst (TList ty) = TList (applyEffSubstTy subst ty)
applyEffSubstTy subst (TRecord fields) =
    TRecord (alistmap (applyEffSubstTy subst) fields)
applyEffSubstTy subst (TVar x) = TVar x

-- Type operations

instantiate (qs, ty) =
    do subst <- sequence [do y <- gensym ; return (q, TVar y) | q <- qs]
       return $ applyTySubst subst ty

{- normalizeType
   Renumber all the type variables in a normal way to allow
   comparing types.
-}
normalizeType :: Type -> State (Int, [(Int, Int)]) Type
normalizeType TBool = return TBool
normalizeType TNum = return TNum
normalizeType (TVar a) = do (ctr, env) <- Control.Monad.State.get
                            case lookup a env of
                              Nothing -> do put (ctr+1, (a, ctr):env)
                                            return $ TVar ctr
                              Just b -> return $ TVar b
normalizeType (TArr s (effs, maybeRho) t) =
    do s' <- normalizeType s
       (ctr, env) <- get
       maybeRho' <- case maybeRho of
                         Nothing -> return Nothing
                         Just rho -> case lookup rho env of
                                       Nothing -> do put (ctr+1, (rho, ctr):env)
                                                     return $ Just ctr
                                       Just rho' -> return $ Just rho'
       t' <- normalizeType t
       return $ TArr s' (nub $List.sort effs, maybeRho') t'

runNormalizeType ty = evalState (normalizeType ty) (0, [])

-- instanceOf: is there a substitution that turns ty2 into ty1? Useful in tests
instanceOf :: Type -> Type -> Either () ()
instanceOf ty1 (TVar x) = return ()
instanceOf TBool TBool = return ()
instanceOf TNum TNum = return ()
instanceOf (TArr s e t) (TArr u f v) = 
    instanceOf t v >>
    instanceOf s u
instanceOf (TList a) (TList b) = instanceOf a b
instanceOf (TRecord a) (TRecord b) = 
    let a' = sortAlist a 
        b' = sortAlist b
    in
      do result <- sequence [if ax == bx then instanceOf ay by else fail ""
                             | ((ax, ay), (bx, by)) <- zip a' b']
         return ()
instanceOf a b = fail ""

unify :: Type -> Type -> Failure (TySubst, RowSubst)
unify s t | s == t = return ([], [])
unify (TVar x) t | not (x `occurs` t) = return ([(x, t)], [])
                 | otherwise = fail("Occurs check failed on " ++ 
                                    show (TVar x) ++ " and " ++ show t)
unify t (TVar x) | not (x `occurs` t) = return ([(x, t)], [])
                 | otherwise = fail("Occurs check failed on " ++ 
                                    show t ++ " and " ++ show (TVar x))
unify TBool TBool = return ([], [])
unify TNum TNum = return ([], [])
unify (TArr s e t) (TArr u f v) = 
    do substEF <- unifyEffectRow e f --BUG? Talpin+Jouvelot, subst this fwd
       let s' = applyTyEffSubstTy substEF s
       let u' = applyTyEffSubstTy substEF u
       let t' = applyTyEffSubstTy substEF t
       let v' = applyTyEffSubstTy substEF v
       substSU <- unify s' u'
       substTV <- unify (applyTyEffSubstTy substSU t')
                        (applyTyEffSubstTy substSU v')
       composeTyEffSubst [substTV, substSU, substEF]
unify (TList a) (TList b) = unify a b
unify (TRecord a) (TRecord b) =
    -- FIXME: this is too strict, it doesn't allow the two to extend a common core.
    let a' = sortAlist a
        b' = sortAlist b
    in
      do substs <- sequence $
                   (do ((ax, ay), (bx, by)) <- zip a' b'
                       [if ax == bx then unify ay by else
                            fail("fields " ++ ax ++ " and " ++ bx ++
                                 " mismatched.")])
         let (tySubsts, rowSubsts) = unzip substs
         subst <- composeTySubst tySubsts
         return (subst, composeRowSubst rowSubsts)
unify a b = fail("Type mismatch between " ++ 
                 show a ++ " and " ++ show b)

unifyAll :: [Type] -> Failure TyEffSubst
unifyAll [] = return ([], [])
unifyAll [x] = return ([], [])
unifyAll (x1:x2:xs) = do (tySubst, rowSubst) <- x1 `unify` x2
                         unifyAll (map (applyEffSubstTy rowSubst . 
                                        applyTySubst tySubst)
                                   (x2:xs))

-- unused
disjoinSubst :: TySubst -> TySubst -> TySubst
disjoinSubst a b =
  [(image bx mapping, applyTySubst subst by) | (bx, by) <- b]
    where mapping = (dom b ++ ftvsSubst b) `zip` ([0..]\\ (dom a ++ ftvsSubst a))
          subst = alistmap TVar mapping

eqUpTo f x y = f x == f y

-- Fails; something wrong with the way substitutions are composed or not.
prop_unify_apply_subst = 
  forAll arbitrary $ \(a :: Type) ->
  forAll arbitrary $ \(b :: Type) -> 
    collect (length$ftvs a, length$ftvs b) $
    either (\_ -> False ==> True) (property . id) $
    do (subst, effSubst) <- a `unify` b
       let e = applyEffSubstTy effSubst $ applyTySubst subst a
       let f = applyEffSubstTy effSubst $ applyTySubst subst b
       return $ eqUpTo runNormalizeType e f

composeTyEffSubst :: [TyEffSubst] -> Failure TyEffSubst
composeTyEffSubst [] = return $ ([],[])
composeTyEffSubst subst =
    -- TBD apply eff substs across types
    let (tySubsts, effSubsts) = unzip subst in
    do addlSubsts <- sequence $
                         onCorresponding unifyAll $ concat tySubsts
       let (addlTySubsts, addlEffSubsts) = unzip addlSubsts
       let substs' = tySubsts ++ addlTySubsts
       let tySubst = flip foldr1 substs'
                 (\s1 s2 -> s1 ++ alistmap (applyTySubst s1) s2)
       if any (\(a,b) -> occurs a b) tySubst then 
          fail "Circular type substitution in composeTySubst" 
        else 
            return (tySubst, composeRowSubst (effSubsts++addlEffSubsts))

composeTySubst subst = liftM fst $ (composeTyEffSubst $ zip subst (repeat []))

prop_composeTySubst = 
    forAll (genEnv 0) $ \a ->
    forAll (genEnv (length a)) $ \b ->
    forAll arbitrary $ \ty ->
    disjointAlist a b && validEnv a && validEnv b ==>
    (do ab <- composeTySubst[a, b]
        return $ applyTySubst ab ty)
    == (return $ (applyTySubst a $ applyTySubst b ty) :: Failure Type)

-- under x = ErrorT (return x)
under = either throwError return -- alt. def.
-- under = maybe (fail "") return  -- def. for MaybeT instead of ErrorT

--
-- Type-n-effect inference algorithm
--

type TypedTerm = Term TyEff

foldUnifyEffectRows :: [EffectRow] -> Failure TyEffSubst
foldUnifyEffectRows [] = return ([], [])
foldUnifyEffectRows [eff] = return ([], [])
foldUnifyEffectRows (eff1:eff2:effs) =
    do effSubst1 <- eff1 `unifyEffectRow` eff2
       let effs' = map (applyTyEffSubstEff effSubst1) (eff2:effs)
       effSubst2 <- foldUnifyEffectRows effs'
       composeTyEffSubst [effSubst1, effSubst2]

prop_foldUnifyEffectRows =
    forAll arbitrary $ \rows ->
        case (do subst <- foldUnifyEffectRows rows
                 return $ allEq (map (applyTyEffSubstEff subst) rows)) of
          Left _ -> True
          Right b -> b

isBaseTy TBool = True
isBaseTy TNum  = True
isBaseTy _     = False

isTyVar (TVar _) = True
isTyVar _        = False

isDBRecordTy (TRecord fields) = all (isBaseTy . snd) fields
isDBRecordTy _                = False

isRecordTy (TRecord fields) = True
isRecordTy _                = False

isDBTableTy (TList ty) = isDBRecordTy ty
isDBTableTy _          = False

applyTyEffSubstTy :: TyEffSubst -> Type -> Type
applyTyEffSubstTy (tySubst, effSubst) ty = applyEffSubstTy effSubst $
                                           applyTySubst tySubst ty

applyTyEffSubstEff :: TyEffSubst -> EffectRow -> EffectRow
applyTyEffSubstEff (_, effSubst) effRow = applyRowSubst effSubst effRow

emptyTyEffSubst :: (TySubst, RowSubst)
emptyTyEffSubst = ([],[])

tyCheckTerms env terms = 
    do results <- sequence [tyCheck env term | term <- terms]
       let (tyEffSubsts, terms') = unzip results
       let (terms'', termTyEffs) = unzip terms'
       let (termTys, termEffs) = unzip termTyEffs
       tyEffSubst <- under $ composeTyEffSubst tyEffSubsts
       eff <- case termEffs of
                [] -> newOpenEmptyRow
                _  -> do addlEffSubst <- under $ foldUnifyEffectRows $ 
                                           map (applyTyEffSubstEff tyEffSubst) termEffs
                         return $ applyTyEffSubstEff addlEffSubst (head termEffs)
       return (tyEffSubst, terms', eff)

-- tyCheck env term infers a type for term in environment env.
-- the environment has type [(Var, QType)];
-- an entry (x, qty) indicates that variable x has the quantified type qty
-- a qTy (ys, ty) indicates the type "forall ys, ty".
tyCheck :: [(Var, QType)] -> Term a
        -> ErrorT String Gensym (TyEffSubst, Term TyEff)
tyCheck env (Unit, _) = 
    do eff <- newOpenEmptyRow
       let tyEff = (TUnit, eff)
       return (emptyTyEffSubst,
               (Unit, tyEff))
tyCheck env (Bool b, _) = 
    do eff <- newOpenEmptyRow
       let tyEff = (TBool, eff)
       return (emptyTyEffSubst,
               (Bool b, tyEff))
tyCheck env (Num n, _) = 
    do eff <- newOpenEmptyRow
       let tyEff = (TNum, eff)
       return (emptyTyEffSubst,
               (Num n, tyEff))
tyCheck env (Table t tys, _) =
    do eff <- newOpenEmptyRow
       let tyEff = (TList (TRecord tys), eff)
       return (emptyTyEffSubst,
               (Table t tys, tyEff))
tyCheck env (Var x, _) =
    {- FIXME: type inference doesn't properly label subterms that have
       free variables; for that matter, it doesn't consistently label the
       whole term. -}
    do eff <- newOpenEmptyRow
       let qTy = fromMaybe (error("Type error: no var " ++ x))
                 $ lookup x env
       ty <- lift $ instantiate qTy
       -- debug("*** instantiated " ++ show qTy ++ " to " ++ show ty) $
       return(emptyTyEffSubst, 
              (Var x, (ty, eff)))
tyCheck env (Do eff m, _) = 
    do rowVar <- lift gensym
       (tyEffSubst, m'@(_, (_, mEff))) <- tyCheck env m
       effSubst <- under $ ([eff], Just rowVar) `unifyEffectRow` mEff
       let effs = applyTyEffSubstEff effSubst ([eff], Just rowVar)
       tyEffSubst' <- under$ composeTyEffSubst [effSubst, tyEffSubst]
       return(tyEffSubst',
              (Do eff m', 
               (TUnit, effs)))
tyCheck env (PrimApp fun args, _) = 
    do (tyEffSubst, args, eff) <- tyCheckTerms env args
       return(tyEffSubst, (PrimApp fun args, (TBool, eff))) -- TBD
tyCheck env (Abs x n, _) = 
    do absEff <- newOpenEmptyRow; argTyVar <- lift gensym
       (tyEffSubst, n'@(_, (nTy, nEff))) <- 
           tyCheck ((x, ([], TVar argTyVar)) : env) n
       let argTy = applyTyEffSubstTy tyEffSubst $ TVar argTyVar
       let arrEff = applyTyEffSubstEff tyEffSubst nEff
       return(tyEffSubst,
              (Abs x n', (TArr argTy arrEff nTy, absEff)))
tyCheck env (DB m, _) = 
    do rowVar <- lift gensym
       (subst@(tySubst, mEffSubst), m'@(_, (mTy, mEff))) <- tyCheck env m
       closingEffSubst <- under (unifyEffectRow mEff ([], Nothing))
       let mEff' = applyTyEffSubstEff closingEffSubst mEff -- (unused)
       subst' <- under$ composeTyEffSubst [closingEffSubst, subst]
       let mTy' = applyTyEffSubstTy subst' mTy
       if isDBTableTy mTy then  
           return (subst',
                   (DB m', (mTy', ([], Just rowVar))))
         else fail("Non-DB type " ++ show mTy ++ " in DB brackets ")
tyCheck env (If c a b, _) =
    do (cTyEffSubst, c'@(_, (cTy, cEff))) <- tyCheck env c
       (aTyEffSubst, a'@(_, (aTy, aEff))) <- tyCheck env a
       (bTyEffSubst, b'@(_, (bTy, bEff))) <- tyCheck env b
       cBaseTyEffSubst <- under (unify cTy TBool)
       abTyEffSubst <- under $ unify aTy bTy
       tyEffSubst <- under $ composeTyEffSubst
                             [aTyEffSubst, bTyEffSubst, cTyEffSubst,
                              cBaseTyEffSubst, abTyEffSubst]
       let ty = applyTyEffSubstTy tyEffSubst bTy
       effSubst1 <- under$ aEff `unifyEffectRow` bEff
       effSubst2 <- under$ (applyTyEffSubstEff effSubst1 aEff)
                             `unifyEffectRow` cEff
       tyEffSubst' <- under$ composeTyEffSubst [effSubst2,effSubst1,tyEffSubst]
       let eff = applyTyEffSubstEff tyEffSubst' aEff
       return (tyEffSubst',
               (If c' a' b', (ty, eff)))
tyCheck env (Nil, _) = 
    do t <- lift gensym
       eff <- newOpenEmptyRow
       return (emptyTyEffSubst, (Nil, (TList (TVar t), eff)))
tyCheck env (Singleton m, _) =
    do (tyEffSubst, m'@(_, (mTy, mEff))) <- tyCheck env m
       return (tyEffSubst,
               (Singleton m', (TList mTy, mEff)))
tyCheck env (Union a b, _) =
    do (aTyEffSubst, a'@(_, (aTy, aEff))) <- tyCheck env a
       (bTyEffSubst, b'@(_, (bTy, bEff))) <- tyCheck env b
       abTyEffSubst <- under $ unify aTy bTy
       tyEffSubst <- under $ composeTyEffSubst
                             [aTyEffSubst, bTyEffSubst, abTyEffSubst]
       let ty = applyTyEffSubstTy tyEffSubst bTy
       effSubst1 <- under$ aEff `unifyEffectRow` bEff
       tyEffSubst' <- under$ composeTyEffSubst [effSubst1,tyEffSubst]
       let eff = applyTyEffSubstEff tyEffSubst' aEff
       return (tyEffSubst',
               (Union a' b', (ty, eff)))
tyCheck env (Record fields, _) =
    let (fieldNames, terms) = unzip fields in
    do (tyEffSubst, terms, eff) <- tyCheckTerms env terms
--        results <- sequence [tyCheck env term | (name, term) <- fields]
--        let (tyEffSubsts, fields') = unzip results
--        let (fieldTerms, fieldTyEffs) = unzip fields'
--        let (fieldTys, fieldEffs) = unzip fieldTyEffs
--        tyEffSubst <- under $ composeTyEffSubst tyEffSubsts
--        eff <- case fieldEffs of
--                 []      -> newOpenEmptyRow
--                 (eff:_) -> return $ applyTyEffSubstEff tyEffSubst eff
       let fieldTys = map (fst.snd) terms
       return (tyEffSubst,
               (Record (zip fieldNames terms),
                (TRecord [(name,ty)| (ty, name) <- zip fieldTys fieldNames],
                 eff)))
tyCheck env (Project m f, _) =
    do rowVar <- lift gensym; a <- lift gensym
       ((tySubst, effSubst), m'@(_, (mTy, mEff))) <- tyCheck env m
       case mTy of
         TVar x ->     -- Note: bogus
                return (((x, TRecord [(f, TVar a)]):tySubst, effSubst),
                        (Project m' f, (TVar a, mEff)))
         TRecord fieldTys ->
                case lookup f fieldTys of
                  Nothing -> fail("no field " ++ f ++ " in record " ++ 
                                  (show $strip m))
                  Just fieldTy ->
                      return ((tySubst, effSubst),
                              (Project m' f, (fieldTy, mEff)))
         _ -> fail("Project from non-record type.")
tyCheck env (App m n, _) = 
    do a <- lift gensym; b <- lift gensym; e <- newOpenEmptyRow
       (mTyEffSubst, m'@(_, (mTy, mEff))) <- tyCheck env m
       (nTyEffSubst, n'@(_, (nTy, nEff))) <- tyCheck env n
       let nEff' = applyTyEffSubstEff mTyEffSubst $ nEff
       let mEff' = applyTyEffSubstEff nTyEffSubst $ mEff
       let nTy' = applyTyEffSubstTy mTyEffSubst $ nTy
       let mTy' = applyTyEffSubstTy nTyEffSubst $ mTy
       subExprTyEffSubst <- under $ composeTyEffSubst [mTyEffSubst, nTyEffSubst]
       
       let mArrTy = TArr (nTy') e (TVar b)
       mArrTyEffSubst <- under $ unify mArrTy mTy'
       let mEff'' = applyTyEffSubstEff mArrTyEffSubst $ mEff'
       let nEff'' = applyTyEffSubstEff mArrTyEffSubst $ nEff'
       
       let resultTy = applyTyEffSubstTy mArrTyEffSubst $ TVar b
       
       let mArrEff = applyTyEffSubstEff mArrTyEffSubst $ e
       
       effSubst <- under $ mEff'' `unifyEffectRow` nEff''
       let subExprEffs = applyTyEffSubstEff effSubst mEff''
       effSubst' <- under $ subExprEffs `unifyEffectRow` mArrEff
       
       let effects = applyTyEffSubstEff effSubst' $
                         subExprEffs
       tyEffSubst <- under $ composeTyEffSubst [effSubst', effSubst,
                                                mArrTyEffSubst,
                                                subExprTyEffSubst]
       
       return (tyEffSubst,
               (App m' n', (resultTy, effects)))
       
tyCheck env (Comp x m n, d) = 
    do (subst, term') <-
            tyCheck env (App (App (Var "concatMap", d)
                              (Abs x n, d), d) m, d)
       let (App (App (Var "concatMap", _)
                 (Abs x' n', _), _) m', tyEff) = term'
       return (subst, (Comp x' m' n', tyEff))

makeInitialTyEnv :: ErrorT String Gensym [(String, QType)]
makeInitialTyEnv = 
    do noEff1 <- newOpenEmptyRow
       noEff2 <- newOpenEmptyRow
       alpha <- lift gensym
       beta <- lift gensym
       return [("concatMap",
                ([alpha, beta],
                 TArr (TArr (TVar alpha) noEff1  (TList (TVar beta))) noEff2
                    (TArr (TList (TVar alpha)) noEff1 (TList (TVar beta))))
               ),
               ("+",
                ([], TArr TNum noEff1
                       (TArr TNum noEff2 TNum))
               )]

infer :: Term a -> ErrorT String Gensym (TypedTerm)
infer term =
    do initialTyEnv <- makeInitialTyEnv
       (_, term') <-
        --    runErrorGensym $ 
               tyCheck initialTyEnv term
       return term'

infer' :: Term' a -> ErrorT String Gensym (TypedTerm)
infer' term = infer (term, undefined)

runInfer = runErrorGensym . infer

runTyCheck env m = runErrorGensym $ 
    do initialTyEnv <- makeInitialTyEnv
       tyCheck (initialTyEnv++env) m

inferTyEffs :: Term () -> ErrorT String Gensym (Type, [Effect])
inferTyEffs m = 
    do (_, (ty, (effs, _))) <- infer m
       return (ty, effs)

inferType :: Term () -> ErrorT String Gensym Type
inferType m = infer m >>= (return . fst . snd)

runInferType = runErrorGensym . inferType

inferEffects m = infer m >>= (return . snd)

inferType' :: Term' () -> ErrorT String Gensym Type
inferType' m = infer' m >>= (return . fst . snd)

inferEffects' :: Term' () -> ErrorT String Gensym [Effect]
inferEffects' m = infer' m >>= (return . fst . snd . snd)

runInferEffects = runErrorGensym . inferEffects

-- UNIT TESTS

unitAssert b = assertEqual "." b True

hasEffects term effects = 
    effects ~=? runErrorGensym (inferEffects' term)

{- funcArgHasNoEffects
   True if the given type is a function taking a functional argument
   and that function is restricted to having no effects.
 -}
funcArgHasNoEffects (TArr (TArr _ ([], Nothing) _) _ _) = True
funcArgHasNoEffects _ = False

tyCheckTests = TestList ["Do Eff1" ~: hasEffects (Do Eff1 (Unit, ())) [Eff1],
                   "Do Eff2" ~: hasEffects (Do Eff2 (Unit, ())) [Eff2],
                   "Apply Eff2ng function" ~: 
                     hasEffects (App (Abs "x" (Do Eff2 (Unit, ()), ()), ()) (Num 7, ()))
                         [Eff2],
                   "Apply const function to Eff2 arg." ~: 
                     hasEffects (App (Abs "x" (Num 9, ()), ()) (Do Eff2  (Unit, ()), ()))
                         [Eff2],
                   "Apply idy function to Eff2 arg." ~: 
                     hasEffects (App (Abs "x" (Var "x", ()), ()) (Do Eff2 (Unit, ()), ()))
                         [Eff2],
                   "Send Eff1ng function to HO function" ~:
                     hasEffects (App
                                 (Abs "x" (App (Var "x",()) (Num 11,()),()),())
                                 (Abs "x" (Do Eff1 (Unit, ()), ()), ()))
                                [Eff1],
                   "Simple application of id to table" ~:
                     (runErrorGensym $ 
                       inferTyEffs (App (Abs "x" (Var "x", ()), ())
                              (Table "wine" [], ()), ()))
                       ~?= (TList (TRecord []), []),
                   "Curried application of id to table" ~:
                     (runErrorGensym . inferTyEffs)
                     (App (App
                              (Abs "x" (Abs "y" (App (Var "x", ())
                                                     (Var "y", ()), ()), ()), ())
                                 (Abs "x" (Var "x", ()), ()), ())
                                 (Table "wine" [], ()), ())
                       ~?= (TList (TRecord []), []),
                   "Curried application, de-/reconstructing record" ~:
                     (runErrorGensym . inferTyEffs) 
                     (App (App
                      (Abs "f" (Abs "x" (App (Var "f",()) (Var "x",()),()),()),())
                      (Abs "x"
                       (Record[("baz", (Project(Var "x",()) "foo", ()))],
                        ()),
                       ()), ())
                      (Record [("foo", (Num 47, ()))], ()), ())
                      ~?= (TRecord[("baz", TNum)], []),
                   "Application of abstraction in pure context" ~:
                         -- expected to fail until we get the kinding disc.
                   unitAssert$funcArgHasNoEffects $
                     (runErrorGensym . inferType)
                     (Abs "p"
                      (DB (Comp "x" (Table "wine" [("wine_id", TNum)], ())
                       (Singleton (Record
                          [("a", (App (Var "p", ())
                                  (Project (Var "x", ()) "wine_id", ()),
                                  ()))],
                          ()), ()),
                       ()), ()), ()),
                    "omega" ~:
                    unitAssert $ isLeft $
                      (runGensym . runErrorT . inferType)
                      (Abs "x" (App (Var "x", ()) (Var "x", ()), ()), ())
                  ]


test_typing1 = 
  let idTy = (TArr (TVar 9) ([], Just 8) (TVar 9)) in
  let concatMapTy = (TArr (TArr (TVar 2) ([], Just 0) (TList (TVar 3)))
                     ([],Just 1) (TArr (TList (TVar 2)) ([],Just 0)
                                           (TList (TVar 3)))) in
  let Right(mArrSubst, _) = unify concatMapTy  (TArr (TVar 4) ([], Just 8) 
                                                (TVar 5)) in
  let argTy = applyTySubst mArrSubst (TVar 4) in
             -- TArr (TVar 2) ([],Just 0) (TList (TVar 3))
  let Right(funcArgSubst, _) = unify argTy idTy in
  let resultTy = (applyTySubst funcArgSubst $ applyTySubst mArrSubst (TVar 5)) in
  (resultTy, funcArgSubst,
   case resultTy of
   TArr (TList (TList (TVar a))) _ (TList (TVar b)) -> a == b)

test_typing = let (_,_,x) = test_typing1 in 
             TestCase (unitAssert x)


-- Number of comprehensions in an expression; a measure of the complexity 
-- of the query.
numComps (Comp x src body, _) = 1 + numComps src + numComps body
numComps (PrimApp _ args, _) = sum $ map numComps args
numComps (Abs _ n, _) = numComps n
numComps (App l m, _) = numComps l + numComps m
numComps (DB m, _) = numComps m
numComps (Singleton body, _) = numComps body
numComps (Record fields, _) = sum $ map (numComps . snd) fields
numComps (Project m _, _) = numComps m
numComps (Union a b, _) = numComps a + numComps b
numComps (Do _ m, _) = numComps m
numComps (Unit, _) = 0
numComps (Bool _, _) = 0
numComps (Num _, _) = 0
numComps (Var _, _) = 0
numComps (Table _ _, _) = 0
numComps (If c a b, _) = numComps c + numComps a + numComps b
numComps (Nil, _) = 0


--
-- QuickCheck term generators
--

smallIntGen :: Gen Int
smallIntGen = elements [0..5]

effRowGen =
    do effs <- elements (subsets [Eff1, Eff2])
       rowVar <- arbitrary
       return (effs, rowVar)

typeGen tyEnv size =
    oneof $ [
         return TBool,
         return TNum
        ] ++
    when (length tyEnv > 0) (do x <- elements tyEnv; return $ TVar x) ++
    whens (size > 0)
        [
         do s <- typeGen tyEnv (size-1)
            t <- typeGen tyEnv (size-1)
            effRow <- effRowGen
            return $ TArr s effRow t,
         do t <- typeGen tyEnv (size-1)
            return $ TList t,
         do n <- smallIntGen :: Gen Int
            fields <- sequence [do t <- typeGen tyEnv (size-1)
                                   return ('f':show i, t) | i <- [0..n]]
            return $ TRecord fields
        ]

termGen fvs size = frequency $
    [(1,                    return (Unit, ())),
     (1, do b <- arbitrary; return (Bool b, ())),
     (1, do n <- arbitrary; return (Num n, ()))
    ] ++
    (whens (not(null(fvs))) [(3, do x <- elements fvs;
                                    return (Var x, ()))]) ++
    whens (size > 0) [
     (1, do e <- arbitrary; 
            m <- termGen fvs (size-1); return (Do e m, ())),
     (3, do x <- varGen
            n <- termGen (x:fvs) (size-1)
            return (Abs x n, ())),
     (6, do m <- termGen fvs (size-1)
            n <- termGen fvs (size-1)
            return $ (App m n, ())),
     (6, do m <- termGen fvs (size-1)
            return $ (DB m, ())),
     (6, do m <- termGen fvs (size-1)
            f <- identGen
            return $ (Project m f, ())),
     (6, do m <- termGen fvs (size-1)
            return $ (Singleton m, ())),
     (18, do n <- smallIntGen
             name <- identGen
             fields <- sequence $ replicate n $
                       do name <- identGen
                          ty <- elements [TBool, TNum]
                          return (name, ty)
             return $ (Table name fields, ())),
     (9, do n <- smallIntGen
            fields <- sequence $ replicate n $
                      do name <- identGen
                         term <- termGen fvs (size-1)
                         return (name, term)
            return $ (Record fields, ())),
     (72, do x <- varGen
             l <- termGen fvs (size-1)
             m <- termGen (x:fvs) (size-1)
             return $ (Comp x l m, ()))
    ]

translatableSyms = []

closedTermGen :: Int -> Gen (Term' (), ())
closedTermGen size = 
--    debug("generating closed term at size " ++ show size) $
    termGen translatableSyms size

oneofMaybe :: [Gen(Maybe a)] -> Gen (Maybe a)
oneofMaybe [] = return Nothing
oneofMaybe (x:xs) = do x' <- x
                       xs' <- oneofMaybe xs
                       case (x', xs') of
                         (Nothing, Nothing) -> return Nothing
                         _ -> oneof (map (return . Just) $ 
                                         asList x' ++ asList xs')

-- Why isn't this bloody thing generating deconstructors??
typedTermGen :: [(Var, QType)] -> Type -> Int -> Gen (Term ())
typedTermGen env ty sz = 
--    debug ("generating term (type " ++ show ty ++ ") at size " ++ show sz) $
    frequency (
    -- variables
    -- (NOTE: presently only gens vars that have ground type, sans quant'rs)
    [(2, return $ (Var x, ())) | (x, (xQs, xTy)) <- env,
                                 xQs == [] && xTy == ty] ++
    -- constructors
    (case ty of
      TNum  -> [(1, do n <- arbitrary; return (Num n, ()))]
      TBool -> [(1, do b <- arbitrary; return (Bool b, ()))]
      TArr s e t -> 
          [(2, do x <- varGen 
                  n <- typedTermGen ((x, ([], s)):(unassoc x env)) t decSz
                  return $ (Abs x n, ()))]
      TRecord fTys -> 
          [(2, do fields <- sequence
                            [do m <- typedTermGen env ty decSz
                                return (lbl, m)
                             | (lbl,ty) <- fTys] :: Gen [(String,Term())]
                  return $ (Record fields, ()))]
      TList ty ->
          [(2, do m <- typedTermGen env ty decSz 
                  return $ (Singleton m, ()))]
          ++ case ty of 
                TRecord fTys ->
                  if not (all (\(_, ty) -> isBaseTy ty) fTys) then [] else
                  [(2, do tab <- identGen
                          return $ (Table ('T':tab) fTys, ()))]
                _ -> []
      _ -> error("Strange type while generating term: " ++ 
                 show ty ++ " (size " ++ show sz ++ ")")
    ) ++
    -- deconstructors
    if (sz <= 0) then [] else (
     [
-- (1, do e <- arbitrary; 
--              m <- typedTermGen env ty decSz; return (Do e m, ())),
      (10, do s <- typeGen [] (intSqrt sz)
              e' <- effRowGen
              m <- typedTermGen env (TArr s e' ty) decSz
              n <- typedTermGen env s decSz
              return $ (App m n, ())),
      (10, do c <- typedTermGen env TBool decSz
              a <- typedTermGen env ty decSz
              b <- typedTermGen env ty decSz
              return $ (If c a b, ()))
     ] ++
     -- Comprehension: a constructor and a destructor
     case ty of
      (TList _) ->
          [(20, do x <- varGen
                   s <- typeGen [] (intSqrt sz)
                   src <- typedTermGen env (TList s) decSz
                   body <- typedTermGen ((x,([],s)):env) ty decSz
                   return (Comp x src body, ()))
          ]
      _ -> []
    )
  )
  where decSz = max (sz-1) 0

closedTypedTermGen ty size = 
--    debug("generating closed term at size " ++ show size) $
    let tyEnv = runErrorGensym makeInitialTyEnv in
    typedTermGen tyEnv ty size

dbTableTypeGen :: Gen Type
dbTableTypeGen = 
    do n <- nonNegInt :: Gen Int
       ty <- elements [TBool, TNum]
       return $ TList (TRecord [('t': show i, ty) | i <- [0..n-1]])

prop_typedTermGen_tyCheck =
  forAll (sized $ typeGen []) $ \ty ->
  forAll (sized $ typedTermGen (runErrorGensym makeInitialTyEnv) ty) $ \m ->
  case runGensym $ runErrorT $ infer m of
    Left _ -> False
    Right (m', (ty', effs)) -> errorMToBool $ unify ty ty'

-- Generic term-recursion functions

entagulate :: (Term a -> b) -> Term a -> Term b
entagulate f (Bool b, d) = (Bool b, f (Bool b, d))
entagulate f (Num n, d) = (Num n, f (Num n, d))
entagulate f (Do eff m, d) = (Do eff (entagulate f m), f (Do eff m, d))
entagulate f (Var x, d) = (Var x, f (Var x, d))
entagulate f (Abs x n, d) = (Abs x (entagulate f n), f (Abs x n, d))
entagulate f (App l m, d) = (App (entagulate f l) (entagulate f m),
                          f (App l m, d))
entagulate f (DB m, d) = (DB (entagulate f m), f (DB m, d))
entagulate f (If c a b, d) =
    (If (entagulate f c)
     (entagulate f a)
     (entagulate f b),
     f (If c a b, d))
entagulate f (Table tab fields, d) = (Table tab fields, f (Table tab fields, d))
entagulate f (Nil, d) = (Nil, f (Nil,d))
entagulate f (Singleton m, d) = (Singleton (entagulate f m),
                              f (Singleton m, d))
entagulate f (Union a b, d) =
    (Union
     (entagulate f a)
     (entagulate f b),
     f (Union a b, d))
entagulate f (Record fields, d) = (Record (alistmap (entagulate f) fields), 
                                f (Record fields, d))
entagulate f (Project m a, d) = (Project (entagulate f m) a,
                              f (Project m a, d))
entagulate f (Comp x src body, d) = 
    (Comp x (entagulate f src) (entagulate f body),
     f (Comp x src body, d))
entagulate f (PrimApp prim args, d) =
    (PrimApp prim (map (entagulate f) args), f (PrimApp prim args, d))
entagulate f (Unit, d) =
    (Unit, f (Unit, d))

-- retagulate :: (Term a -> a) -> Term a -> Term a
-- retagulate f (Bool b, d) = (Bool b, f (Bool b, d))
-- retagulate f (Num n, d) = (Num n, f (Num n, d))
-- retagulate f (Do eff m, d) = (Do eff (retagulate f m),
--                               f (Do eff (retagulate f m), d))
-- retagulate f (Var x, d) = (Var x, f (Var x, d))
-- retagulate f (Abs x n, d) = (Abs x (retagulate f n),
--                              f (Abs x (retagulate f n), d))
-- retagulate f (App l m, d) = (App (retagulate f l) (retagulate f m),
--                           f (App (retagulate f l) (retagulate f m), d))
-- retagulate f (DB m, d) = (DB (retagulate f m), f (DB (retagulate f m), d))
-- retagulate f (If c a b, d) =
--     (If (retagulate f c)
--      (retagulate f a)
--      (retagulate f b),
--      f (If (retagulate f c)
--         (retagulate f a)
--         (retagulate f b), d))
-- retagulate f (Table tab fields, d) = (Table tab fields, f (Table tab fields, d))
-- retagulate f (Singleton m, d) = (Singleton (retagulate f m),
--                               f (Singleton (retagulate f m), d))
-- retagulate f (Record fields, d) = (Record (alistmap (retagulate f) fields), 
--                                 f (Record (alistmap (retagulate f) fields), d))
-- retagulate f (Project m a, d) = (Project (retagulate f m) a,
--                               f (Project (retagulate f m) a, d))
-- retagulate f (Comp x src body, d) = 
--     (Comp x (retagulate f src) (retagulate f body),
--      f (Comp x (retagulate f src) (retagulate f body), d))

strip = entagulate (const ())

-- Arbitraries

instance Arbitrary Effect where
    arbitrary = elements [Eff1, Eff2]

-- instance Arbitrary [Effect] where
--     arbitrary = arbSubset [Eff1,Eff2] -- elements (subsets [Eff1, Eff2])

-- instance Arbitrary t => Arbitrary (Maybe t) where
--     arbitrary = oneof [return Nothing,
--                        fmap Just arbitrary]

-- instance Arbitrary EffectRow where
--     arbitrary =
--         do effs <- arbSubset [Eff1,Eff2] -- elements (subsets [Eff1, Eff2])
--            rowVar <- arbitrary
--            return (effs, rowVar)

instance Arbitrary Type where
    arbitrary = 
        oneof
          [ return TBool
          , return TNum
          , do s <- arbitrary
               t <- arbitrary
               effs <- arbSubset [Eff1,Eff2]
               rho <- arbitrary
               return (TArr s (effs, rho) t)
          , do x <- posInt
               return (TVar x)
          ]

--
-- QuickCheck Tests
--

-- Generators

listGen :: Int -> Gen a -> Gen [a]
listGen 0 gen = oneof [ return [], do x <- gen
                                      xs <- listGen 0 gen
                                      return (x : xs)]
listGen n gen = do x <- gen
                   xs <- listGen (n-1) gen
                   return (x : xs)

identCharGen :: Gen Char
identCharGen = oneof $ map return (['a'..'z'] ++ ['A'..'Z'] ++ ['_'])

identGen = listGen 1 identCharGen

varGen = (return ('x':)) `ap` identGen

pairGen :: Gen a -> Gen b -> Gen (a, b)
pairGen aGen bGen = do a <- aGen; b <- bGen; return (a, b)

