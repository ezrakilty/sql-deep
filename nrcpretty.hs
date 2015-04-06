module NRCPretty where

import NRC
import SQL
import ListKit

-- Pretty-printing

class Pretty t where
  pretty :: t -> String

instance Pretty Op where
  pretty Plus = " + "
  pretty Eq = " = "
  pretty Less = " < "
  pretty Divide = " / "
  pretty Times = " * "
  pretty Minus = " - "

instance Pretty (Term' a) where
  pretty (Unit) = "()"
  pretty (Bool b) = show b
  pretty (Num n) = show n
  pretty (PrimApp f args) = f ++ "("++mapstrcat "," (pretty.fst) args ++")"
  pretty (Var x) = x
  pretty (Abs x n) = "(fun " ++ x ++ " -> " ++ (pretty.fst) n ++ ")"
  pretty (App l m) = (pretty.fst) l ++ " " ++ (pretty.fst) m
  pretty (Do e m) = "do " ++ show e ++ "; " ++ (pretty.fst) m
  pretty (DB m) = "db("++(pretty.fst) m++")"
  pretty (Table tbl t) = "table " ++ tbl ++ " : " ++ show t
  pretty (If c a b) = "(if " ++ (pretty.fst) c ++ " then " ++ (pretty.fst) a ++ 
                      " else " ++ (pretty.fst) b ++ " )"
  pretty (Singleton m) = "[" ++ (pretty.fst) m ++ "]" 
  pretty (Nil) = "[]"
  pretty (Union m n) = "("++(pretty.fst) n++" ++ "++(pretty.fst) n++")"
  pretty (Record fields) = 
      "{" ++ mapstrcat "," (\(l,m) -> l ++ "=" ++(pretty.fst) m) fields++ "}"
  pretty (Project m l) = "("++(pretty.fst) m++"."++l++")"
  pretty (Comp x m n)= "for ("++x++" <- "++(pretty.fst) m++") " ++ (pretty.fst)n

instance Pretty Query where
  pretty (QExists q) = "exists (" ++ pretty q ++ ")"
  pretty (Select{rslt=rslt, tabs=tabs, cond=cond}) = 
         "select " ++ mapstrcat ", " (\(alias, q) -> pretty q ++ " as " ++ alias) rslt ++ 
         (if null tabs then "" else
         " from " ++ mapstrcat ", " (\(tableExpr, al, ty) -> 
                                     (case tableExpr of
                                        Imm name -> name
                                        SubQuery q -> "(" ++ pretty q ++ ")")
                                     ++ " as " ++ al) 
                         tabs) ++ 
         " where " ++ pretty_cond cond
                   where pretty_cond [] = "true"
                         pretty_cond cond = mapstrcat " and " pretty cond
  pretty (QOp lhs op rhs) = pretty lhs ++ pretty op ++ pretty rhs
  pretty (QRecord fields) = "{"++ mapstrcat ", "
                               (\(lbl,expr) -> 
                                    lbl ++ "=" ++ show expr) fields
                          ++ "}"
  pretty (QNum n) = show n
  pretty (QRownum) = "row_number() over ()"
  pretty (QBool True) = "true"
  pretty (QBool False) = "false"
   
  pretty (QField a b) = a ++ "." ++ b

  pretty (QUnion a b) = pretty a ++ " union all " ++ pretty b
  pretty (QNot b) = "not " ++ pretty b
  pretty (QIf c t f) = "if " ++ pretty c ++ " then " ++ pretty t
                       ++ " else " ++ pretty f
