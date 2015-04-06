module SQL where

import Basics
import Test.QuickCheck

--
-- Queries
--

data Op = Eq | Less
        | Plus | Minus | Times | Divide
        deriving(Eq, Show)

data UnOp = Min | Max | Count | Sum | Average
        deriving (Eq, Show)

data TableExpr = Imm String | SubQuery Query
        deriving(Eq,Show)

-- Query: the type of SQL queries, select ... from ... where ...
data Query = Select {rslt :: [(Field, Query)],             -- make this a list
                     tabs :: [(TableExpr, Field, Type)],
                     cond :: [Query]
                    }
           | QRownum
           | QNum Integer
           | QBool Bool
           | QNot Query
           | QOp Query Op Query
           | QField String String
           | QRecord [(Field, Query)]
           | QUnion Query Query
           | QIf Query Query Query
           | QExists Query
        deriving(Eq, Show)

{- Basic functions on query expressions -}

-- freevarsQuery :: Query -> [String]
-- freevarsQuery (q@(Select _ _ _)) = 
--     (map (\(_, q) -> freevarsQuery q) (rslt q))
--     `u`
--     (union $ map freevarsQuery (cond q))
-- freevarsQuery (QOp lhs op rhs) = nub (freevarsQuery lhs ++ freevarsQuery rhs)
-- freevarsQuery (QRecord fields) = concatMap (freevarsQuery . snd) fields
-- freevarsQuery _ = []

isQRecord (QRecord _) = True
isQRecord _ = False

-- a groundQuery is a *real* SQL query--one without variables or appl'ns.
groundQuery :: Query -> Bool
groundQuery (qry@(Select _ _ _)) =
    all groundQueryExpr (cond qry) &&
    all groundQueryExpr (map snd (rslt qry))
groundQuery (QUnion a b) = groundQuery a && groundQuery b
groundQuery (QExists qry) = groundQuery qry
groundQuery (QRecord fields) = all (groundQuery . snd) fields
groundQuery (QOp b1 _ b2) = groundQuery b1 && groundQuery b2
groundQuery (QNum _) = True
groundQuery (QBool _) = True
groundQuery (QField _ _) = True
groundQuery (QNot a) = groundQuery a

-- a groundQueryExpr is a query expression: the SELECT clause of a query.
groundQueryExpr :: Query -> Bool
groundQueryExpr (qry@(Select _ _ _)) = False
groundQueryExpr (QUnion a b) = False
groundQueryExpr (QExists qry) = groundQuery qry
groundQueryExpr (QRecord fields) = all (groundQueryExpr . snd) fields
groundQueryExpr (QOp b1 _ b2) = groundQueryExpr b1 && groundQueryExpr b2
groundQueryExpr (QNot a) = groundQueryExpr a
groundQueryExpr (QNum _) = True
groundQueryExpr (QBool _) = True
groundQueryExpr (QField _ _) = True
groundQueryExpr (QIf c a b) = all groundQueryExpr [c,a,b]


-- sizeQuery: the number of terms in the query
--   Used for evaluating test data
sizeQuery :: Query -> Integer
sizeQuery (q@(Select _ _ _)) = (sum $ map (sizeQuery.snd) (rslt q))
                               + (sum $ map sizeQuery (cond q))
sizeQuery (QNum n) = 1
sizeQuery (QRownum) = 1
sizeQuery (QBool b) = 1
sizeQuery (QNot q) = 1 + sizeQuery q
sizeQuery (QOp a op b) = 1 + sizeQuery a + sizeQuery b
sizeQuery (QField t f) = 1
sizeQuery (QRecord fields) = sum [sizeQuery n | (a, n) <- fields]
sizeQuery (QUnion m n) = sizeQuery m + sizeQuery n
sizeQuery (QIf c a b) = sizeQuery c + sizeQuery a + sizeQuery b
sizeQuery (QExists q) = 1 + sizeQuery q


instance Arbitrary Op where
    arbitrary = oneof [return Eq, return Less]
