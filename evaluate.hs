module Evaluate where

import Debug
import Basics
import NRC
import Translate
import ListKit
import NRCPretty
import Maybe (fromMaybe)

-- --
-- --   Evaluation
-- --

-- type RuntimeTerm = Term (Maybe Query)

fromValue :: Value -> TypedTerm
fromValue VUnit = (Unit, undefined)
fromValue (VBool b) = (Bool b, undefined)
fromValue (VNum n) = (Num n, undefined)
fromValue (VList xs) = foldr1 union (map singleton $ map fromValue xs)
    where union x y = (x `Union` y, undefined)
          singleton x = (Singleton x, undefined)
fromValue (VRecord fields) = (Record (alistmap fromValue fields), undefined)
fromValue (VAbs x n env) = foldr (\(y,v) -> substTerm y (fromValue v))
                           (Abs x n, undefined) env

concatVLists xs = VList $ concat [x | (VList x)<-xs]

appPrim "+" [(VNum a), (VNum b)] = VNum (a+b)
appPrim p _ = error("Unknown primitive" ++ p)

eval :: Env -> TypedTerm -> (Value, [Effect])
eval env (Unit, _) = (VUnit, [])
eval env (Bool b, q) = (VBool b, [])
eval env (Num n, q) = (VNum n,[])
eval env (PrimApp prim args, q) = 
    let (vArgs, effs) = unzip $ map (eval env) args in
    (appPrim prim vArgs, concat effs)
eval env (Var x, q) =
    let v = 
         fromMaybe(error("Variable " ++ x ++ " not found in env " ++ show env ++
                         " while evaluating term.")) $
         lookup x env in
    (v, [])
eval env (Abs x n, q) = (VAbs x n env', [])
    where env' = filter (\(a,b) -> a `elem` fvs n) env
eval env (App l m, q) = 
    let (v, vEff) = eval env l in
    let (w, wEff) = eval env m in
    case v of
      (VAbs x n env') -> 
          let (r, bodyEff) = eval ((x,w):env') n in
          (r, vEff ++ wEff ++ bodyEff)
      _ -> error "non-function applied"
eval env (Do eff m, q) = 
    let (v, effs) = eval env m in
    (v, eff : effs)
eval env (DB m, _) =
--    debug("evaling database term " ++ show m) $
    -- Should use environment instead of fromValue
    let m' = normTerm [] (foldr (\(y,v) -> substTerm y (fromValue v)) m env) in
--    debug("normalized to " ++ show m') $
    let q = compileTerm m' in
    debug ("Performing query " ++ pretty q) $
      (VList [], [])    
eval env (Table name fields, q) = 
    (VList [], [])
eval env (If c a b, _) =
    let (VBool t, eff) = eval env c in
    let (result, eff') = if t then eval env a else eval env b in
    (result, eff++eff')
eval env (Nil, _) =
    (VList [], [])
eval env (Singleton body, q) =
    let (v, eff) = eval env body in
    (VList [v], eff)
eval env (Union m n, _) =
    let (VList v, eff) = eval env m in
    let (VList w, eff') = eval env n in
    (VList $ v ++ w, eff ++ eff')
eval env (Record fields, q) =
    let (vFields, effs) = unzip [let (value, eff) = eval env term in
                                 ((name, value), eff)
                                 | (name, term) <- fields] in
    (VRecord vFields, concat effs)
eval env (Project m f, q) =
    let (v, vEff) = eval env m in
    case v of
      VRecord fields -> 
          let vField = fromMaybe(error$ "No field " ++ f ++ " in " ++ 
                                      show v ++ "(" ++ show m ++ ")") $
                       lookup f fields
          in
            (vField, vEff)
      _ -> error("Non-record value " ++ show v ++ " target of projection " ++ 
                 show(Project m f))
eval env (Comp x src body, q) =
    let (vSrc, effSrc) = eval env src in
    case vSrc of
      (VList elems) -> 
          let (results, effs) = 
                        unzip [eval ((x,v):env) body
                               | v <- elems] in
          (concatVLists results, concat effs)
      _ -> error("Comprehension source was not a list.")

run = eval initialEnv

evalQuery q = 
    let m' = normTerm [] q in
    let q = compileTerm m' in
    debug("query is " ++ pretty q) $
    (q,True)


type Env = [(Var, Value)]
data Value' = VUnit | VBool Bool | VNum Integer
            | VList [Value]
            | VRecord [(String, Value)]
            | VAbs Var TypedTerm Env
        deriving (Eq, Show)
type Value = (Value')

initialEnv :: Env
initialEnv =
    []
--     [("+",
--       ((VAbs "x" (Abs "y"
--                   (PrimApp "+" [(Var "x", (TNum, openEpe), (Var "y", TNum)],
--                    Just (QOp (QVar "x") Plus (QVar "y"))), TNum) []),
--        Just (QAbs "x" (QAbs "y" (QOp (QVar "x") Plus (QVar "y"))))))]

