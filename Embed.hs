module Embed where

import Basics
import NRC

(!) x = (x, ())

-- | A dummy value, or zero-width record.
unit :: Term()
unit = (!) Unit

-- -- | A polymorphic way of embedding constants into a term.
-- class Constable a where
--     -- | Lift a constant value into a query.
--     -- @Constable@ types currently include @Bool@ and @Integer@.
--     cnst :: a -> Term()
-- instance Constable Bool    where cnst b = return ((!)(Bool b))
-- instance Constable Integer where cnst n = return ((!)(Num n))
-- instance Constable String  where cnst s = return ((!)(String s))

-- | Apply some primitive function, such as @(+)@ or @avg@, to a list
-- of arguments.
primApp :: String -> [Term()] -> Term()
primApp f args =  (!) (PrimApp f args)

-- -- | Create a functional abstraction.
-- abs :: (String -> Term()) -> Term()
-- abs fn = do
--   n <- gensym
--   let x = '_' : show n
--   body <- fn x
--   return $ (!) $ Abs x body

-- | Apply a functional term to an argument.
app :: Term() -> Term() -> Term()
app l m = (!) (App l m)

-- | A reference to a named database table; second argument is its
-- schema type.
table :: Tabname -> [(Field, Type)] -> Term()
table tbl ty = (!) $ Table tbl ty

-- | A condition between two terms, as determined by the boolean value
-- of the first term.
ifthenelse :: Term() -> Term() -> Term() -> Term()
ifthenelse c t f = (!) (If c t f)

-- | A singleton collection of one item.
singleton :: Term() -> Term()
singleton x = (!) (Singleton x)

-- | An empty collection.
nil :: Term()
nil = (!) Nil

-- | The union of two collections
union :: Term() -> Term() -> Term()
union l r = (!) (Union l r)

-- | Construct a record (name-value pairs) out of other terms; usually
-- used, with base values for the record elements, as the final
-- result of a query, corresponding to the @select@ clause of a SQL
-- query, but can also be used with nested results internally in a
-- query.
record :: [(String, Term())] -> Term()
record fields = (!) (Record fields)

-- | Project a field out of a record value.
project :: Term() -> String -> Term()
project expr field = (!) (Project expr field)

-- | For each item in the collection resulting from the first
-- argument, give it to the function which is the second argument
-- and evaluate--this corresponds to a loop, or two one part of a
-- cross in traditional SQL queries.
foreach :: String -> Term() -> Term() -> Term()
foreach x src body = (!)(Comp x src body)

-- | Filter the current iteration as per the condition in the first
-- argument. Corresponds to a @where@ clause in a SQL query.
having :: Term() -> Term() -> Term()
having cond body = ifthenelse cond body nil

var x = (!)(Var x)
