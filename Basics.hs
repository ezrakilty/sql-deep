module Basics where

type Field = String
type Tabname = String

type Var = String

type TyVar = Int

data Effect = Eff1 | Eff2
    deriving (Eq,Show,Ord)

type EffectRow = ([Effect], Maybe Int)

data Type = TBool | TNum | TUnit | TList Type
          | TArr Type EffectRow Type
          | TRecord [(String, Type)]
          | TVar TyVar
    deriving (Eq, Show)
