{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

import Prelude hiding (catch)
import Control.Exception (catch, throwIO, evaluate)
import Control.Monad.State hiding (when, join)
import List (nub, (\\), sort, sortBy, groupBy, intersperse, transpose)
import Maybe (fromJust, isJust, fromMaybe)
import Control.Monad.Error hiding (when, join)
import Foreign (unsafePerformIO)
import Test.HUnit hiding (State, assert)
import Test.QuickCheck hiding (promote)
import QCUtils
import QCConfig

import FPKit
import ListKit
import StringKit
import Debug

import Basics
import SQL
import Env
import Evaluate
import NRC
import Gensym
import NRCPretty
import Translate

-- Database schemas (flat)

type TableSchema = [(String, Type)]
type Schema = [(String, TableSchema)]

-- Database instances (flat relational data)
data BaseData = DString String | DNum Int | DBool Bool | DUnit
    deriving (Eq,Show)
type TableRow = [(String, BaseData)]
type TableInstance = [TableRow]
type Instance = [(String, TableInstance)]

-- a table instance is only valid if each row maps the same fields
validateTableInstance :: TableInstance -> Bool
validateTableInstance inst = allEq $ map (sort . map fst) inst

-- Nested data

data Data = B BaseData | DList [Data] | DRecord [(String, Data)]
--          | DArr (Data -> Data)
    deriving (Eq,Show)

instance Pretty Data where
    pretty (B (DString x)) = show x
    pretty (B (DNum x)) = show x
    pretty (B (DBool x)) = show x
    pretty (B DUnit) = "()"
    pretty (DList xs) = "[" ++ mapstrcat ", " pretty xs ++ "]"
--     pretty (DRecord fields) = "(" ++ concat (intersperse ", " [lbl ++ "=" ++ pretty val | (lbl, val) <- fields]) ++ ")"
    pretty (DRecord fields) = "(" ++ mapstrcat ", "
                                       (\(lbl, val) -> lbl ++ "=" ++ pretty val)
                                       fields
                              ++ ")"

prettyRow :: [Int] -> [(String, String)] -> String
prettyRow widths alist =
    concat $ intersperse " " [rpad w str | (w, (_, str)) <- zip widths alist]

{- Pretty-printing for flat instances -}

-- Given a list of matching alists, give the 
-- colWidths :: [[(String, String)]] -> [(String, Int)]
-- colWidths rows = alistmap maximum $
--                  untransposeAlists [[(lbl, length str) | (lbl, str) <- row] | row <- rows]

-- colNames :: TableInstance -> [String]
-- colNames tinst =
--     let rows = normalizeTableInstance tinst in
--     map fst (head rows)  -- ignore subsequent rows; assume table has
--                          -- been validated

-- tableMap :: (BaseData -> a) -> TableInstance -> [[(String, a)]]
-- tableMap f rows =
--     [[(lbl, f val) | (lbl, val) <- row] | row <- rows]

-- normalizeTableInstance :: TableInstance -> TableInstance
-- normalizeTableInstance tinst = 
--     map sortAlist tinst

-- prettyInst tables = 
--     do (name, tinst) <- tables
--        [name ++ ":\n" ++
--         let rows = normalizeTableInstance tinst in
--         let prettyFields = tableMap pretty rows in
--         let cw = map snd $ colWidths prettyFields in
--         mapstrcat "\n" (prettyRow cw) prettyFields]

{- Deep-type schemafication and reassembly -}

data Heritage = Heritage (String, [Heritage])
             deriving (Eq, Show)

extendTable (name, cols) (cname, ctype) = 
    (name, (cname, ctype) : cols)

schemafor :: Type -> (Schema, Heritage)
schemafor (TList ty) = let (tsch, (sch, par)) = schemaforRow "main" ty in
                       (tsch : sch, par)
schemafor ty = error ("Not a schema type: " ++ show ty)

schemaforCol :: String -> Type -> (Type, (Schema, [Heritage]))
schemaforCol tableName (TList ty) =
    let (tsch, (sch, par)) = schemaforRow tableName ty in
    (TUnit, (tsch : sch, [par]))
schemaforCol tableName (TBool) = (TBool,  ([], []))
schemaforCol tableName (TNum) =  (TNum,   ([], []))
schemaforCol tableName (TUnit) = (TUnit,  ([], []))
schemaforCol tableName t@(TArr _ _ _) = error ("Not a column type: " ++ show t)
schemaforCol tableName t@(TRecord _) = error ("Not a column type: " ++ show t)
schemaforCol tableName t@(TVar _) = error ("Not a column type: " ++ show t)

schemaforRow :: String -> Type -> ((String, [(String, Type)]),
                                   (Schema, Heritage))
schemaforRow tableName (TRecord fields) = 
    let (dbfields, schPar) =
            unzip [((f, ty), sch)
                   | (f, fty)  <- fields,
                     let (ty, sch) = schemaforCol (tableName++"_"++f) fty]
    in
    let (schemas, parenthoods) = unzip schPar in
    ((tableName, ("_id", TNum) : ("_parent", TNum) : dbfields),
     (concat schemas, Heritage(tableName, concat parenthoods)))
    -- FIXME: Need name for ""
schemaforRow tableName ty = error ("Not a row type: " ++ show ty)

test_schemafor = 
    schemafor (TList (TRecord[("a", TNum), ("b", TBool),
                              ("c", TList (TRecord[("d", TNum)]))]))
    ~?= ([("main",[("_id",TNum),("_parent",TNum),
                   ("a",TNum),("b",TBool),("c",TUnit)]),
          ("main_c",[("_id",TNum),("_parent",TNum),("d",TNum)])],
         Heritage ("main",[Heritage ("main_c",[])]))

join :: [Int] -> [(Int, [a])] -> [[a]]
join ids foreigns = map (\id -> Maybe.fromMaybe [] $ lookup id foreigns) ids

-- lookupHeritage: From a list of Heritage trees, find the one
--   carrying the given label
lookupHeritage :: String -> [Heritage] -> Maybe Heritage
lookupHeritage nm xs = do ph <- lookup nm (unHeritageEm xs)
                          return (Heritage(nm, ph))
    where unHeritage (Heritage x) = x
          unHeritageEm xs = map unHeritage xs

-- TBD: remove the nms argument
transposeAlists :: [String] -> [(String, [a])] -> [[(String, a)]]
transposeAlists nms cols | all (isNull . snd) cols = []
transposeAlists nms cols = [(nm, head (fromJust(lookup nm cols)))| nm <- nms]
                           : transposeAlists nms 
                              [(nm, tail (fromJust(lookup nm cols)))| nm <- nms]

test_transposeAlists =
    transposeAlists ["a", "b"] [("a", [1,2,3]), ("b", [4,5,6])]
          ~?=
       [[("a",1),("b",4)],[("a",2),("b",5)],[("a",3),("b",6)]]

untransposeAlists :: [[(String, a)]]
                  -> [(String, [a])] 
untransposeAlists rows = [(fst (head col), map snd col)
                          | col <- transpose rows]

uscoreJoin path obj = if path == "" then obj else path ++  "_" ++ obj

alistKeys :: [(a,b)] -> [a]
alistKeys = map fst

reass :: String -> Schema -> Heritage -> Instance -> Data
reass path sch (Heritage(table, chilluns)) inst =
    let Just tSch = lookup table sch in
    let Just rawData = lookup table inst in
    let fieldNms = alistKeys tSch in
    let pathTable = uscoreJoin path table in
    let colData :: [(String, [Data])] = 
            do nm <- fieldNms -- for each column
               [case lookupHeritage (pathTable ++ "_" ++ nm) chilluns of
                  Nothing -> (nm, map (B . fromJust . lookup nm) rawData)
                  Just chTable -> 
                      let DList l = reass pathTable sch chTable inst in
                      let groups = map (\xs -> (fst(head xs), 
                                                map unDRecord $ map snd xs)) $
                                   groupOn fst $ sortOn fst
                                   [(parentIdFromData row, row) | row <- l]
                                   :: [(Int, [[(String, Data)]])]
                      in
                        (nm, map DList $ map (map DRecord) $ 
                               (join (map rowId rawData) groups))]
    in
      DList $ map DRecord $ transposeAlists fieldNms colData

unDRecord (DRecord row) = row
unDRecord _ = error "unDRecord applied to non-DRecord"

parentId row =
    case lookup "_parent" row of
      Just(DNum id) -> id
      _ -> error "parentId: row had no int field parent"

parentIdFromData x =
    let DRecord row = x in
    case lookup "_parent" row of
      Just(B(DNum id)) -> id
      _ -> error "parentIdFromData: data was not a record with int field parent"

rowId row = 
    case lookup "_id" row of
      Just(DNum id) -> id
      _ -> error "rowId: row had no int field id"

-- fixup takes a nested instance containing _id and _parent columns
-- and filters those out.
fixup :: Data -> Data
fixup (DList rows) =
    DList $ 
          do (DRecord fields) <- rows
             [(DRecord [(nm, fixup val)
                        | (nm,val) <- fields,
                        nm /= "_id" && nm /= "_parent"])]
fixup (DRecord _) = error "fixup expected list-of-records or base"
fixup (B b) = B b

{------------------------------------ Tests -----------------------------------}

test_instance = [("main", [[("a", DBool False), ("_id", DNum 1)]]),
                 ("main_x", [[("_parent", DNum 1), ("z", DBool True)],
                            [("_parent", DNum 1), ("z", DBool False)]])]

test_reass = TestList[
                  reass "" [("main", [("a", TBool), ("x", TNum), ("_id", TNum)]),
                         ("main_x", [("z", TBool), ("_parent", TNum)])]
                        (Heritage("main", [Heritage("main_x", [])]))
                        [("main", [[("a", DBool False), ("_id", DNum 1)]]),
                         ("main_x", [[("_parent", DNum 1), ("z", DBool True)]])]
                  ~?= DList [DRecord [("a",B (DBool False)),
                                      ("x",DList [DRecord [("z",B (DBool True)),
                                                                ("_parent",B (DNum 1))]]),
                                      ("_id",B (DNum 1))]],
                  reass "" [("main", [("a", TBool), ("x", TNum), ("_id", TNum)]),
                         ("main_x", [("z", TBool), ("_parent", TNum)])]
                        (Heritage("main", [Heritage("main_x", [])]))
                        [("main", [[("a", DBool False), ("_id", DNum 1)]]),
                         ("main_x", [[("_parent", DNum 1), ("z", DBool True)],
                                     [("_parent", DNum 1), ("z", DBool False)]])]
                  ~?= DList [DRecord [("a",B (DBool False)),
                                      ("x",DList [DRecord [("z",B (DBool True)),
                                                                ("_parent",B (DNum 1))],
                                                       DRecord [("z",B (DBool False)),
                                                                ("_parent",B (DNum 1))]]),
                                      ("_id",B (DNum 1))]]
                     ,
                  fixup (reass "" [("main",[("_id",TNum),("_parent",TNum),("ys",TUnit)]),("main_ys",[("_id",TNum),("_parent",TNum),("nomen",TBool)])]
                        (Heritage ("main",[Heritage ("main_ys",[])]))
                        [("main", [[("_id", DNum 1), ("ys", DNum 0)],
	                           [("_id", DNum 2), ("ys", DNum 0)],
	                           [("_id", DNum 3), ("ys", DNum 0)]]),
                         ("main_ys", [[("_parent", DNum 1), ("_id", DNum 1), ("nomen", DString "Ezra")],
                                      [("_parent", DNum 1), ("_id", DNum 2), ("nomen", DString "Joe")],
                                      [("_parent", DNum 2), ("_id", DNum 3), ("nomen", DString "Sal")]
                                     ])
                        ])
                  ~?= 
                  DList [DRecord [("ys",DList [DRecord [("nomen",B (DString "Ezra"))],DRecord [("nomen",B (DString "Joe"))]])],DRecord [("ys",DList [DRecord [("nomen",B (DString "Sal"))]])],DRecord [("ys",DList [])]]
                     ]

--
-- Big QuickCheck properties
--

prop_eval_safe =
    forAll (sized closedTermGen) $ \m ->
    case runGensym $ runErrorT $ infer m of
      Left _ -> False ==> False
      Right _ -> label "successful" $
                 let m' = runErrorGensym $ infer m in
                   propertyDefined $
                     (eval initialEnv $! m')

prop_eval_pure_safe = 
    forAll dbTableTypeGen $ \ty ->
    forAll (sized (closedTypedTermGen ty)) $ \m' ->
    let m = (DB m', ()) in
    --debug ("Typechecking " ++ show m) $
    case runGensym $ runErrorT $ infer m of
      Left _ -> label "ill-typed" $ property True
      Right (_, (ty, eff)) -> 
          isDBTableTy ty ==>
          debug ("Trying " ++ (pretty $ fst m)) $
          --collect (numComps m) $ 
                  let m' = runErrorGensym $ infer m in
                  --(eval initialEnv $! m') `seq` 
                  let (q, ok) = (evalQuery $! m') in
                  collect (sizeQuery q) $ 
                          errorAsFalse $
                          ok

-- prop_norm_sound env = eval env . normTerm env == eval env

prop_dyn_stat_effs_agree = forAll (sized closedTermGen) $ \m -> 
  case errorAsNothing (runErrorGensym $! infer m) of
    Nothing -> False ==> False
    Just (m', (ty, (statEffs, _))) ->
        collect (runNormalizeType ty) $ 
        let m' = runErrorGensym $ infer m in
        let (_, dynEffs) = eval initialEnv m' in
        True ==> dynEffs `setEq` statEffs

{----------------------------------- MAIN -----------------------------------}

main = quickCheckWith (stdArgs {maxSize = 10}) prop_eval_pure_safe

-- Unit tests

test_all = TestList [test_schemafor, test_transposeAlists, test_reass,
                     test_compileNested]
