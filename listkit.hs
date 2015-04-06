module ListKit where

import List

{- List utilities -}

isNull [] = True
isNull _  = False

unassoc a = filter ((/= a) . fst)

nubassoc [] = []
nubassoc ((x,y):xys) = (x,y) : (nubassoc $ unassoc x xys)

graph f xs = [(x, f x) | x <- xs]
alistmap f = map (\(a, b) -> (a, f b))

bagEq a b = a \\ b == [] && b \\ a == []

setEq a b = (nub a) `bagEq` (nub b)

u a b = nub (a ++ b)

union lists = nub $ concat lists

contains a b = null(b \\ a)

setMinus :: Ord a => [a] -> [a] -> [a]
setMinus xs ys = nub $ sort $ xs \\ ys

(\\\) :: Ord a => [a] -> [a] -> [a]
(\\\) = setMinus

allEq [] = True
allEq (x:xs) = all (== x) xs

disjointAlist [] _ = True
disjointAlist _ [] = True
disjointAlist xs ((a,b):ys) =
    (not $ any ((== a) . fst) xs) && disjointAlist xs ys

sortOn f l = sortBy (\x y -> f x `compare` f y) l

groupOn f l = groupBy (\x y -> f x == f y) l

asList Nothing = []
asList (Just x) = [x]

-- zipAlist: given two alists with the same domain,
-- returns an alist mapping each of those domain values to
-- the pair of the two corresponding values from the given lists.
zipAlist xs ys = 
    let xsys = zip (sortAlist xs) (sortAlist ys) in
    if not $ and [x == y | ((x, a), (y, b)) <- xsys] then 
        error "alist mismatch in zipAlist"
    else [(x, (a, b)) | ((x, a), (y, b)) <- xsys]

mapstrcat :: String -> (a -> String) -> [a] -> String
mapstrcat glue f xs = concat $ List.intersperse glue (map f xs)


-- shadow: given two alists, return the elements of the first that
-- are NOT mapped by the second
shadow as bs = [(a,x) | (a,x) <- as, a `notElem` domBs]
    where domBs = map fst bs

validEnv xs = length (nub $ map fst xs) == length xs

mr agg xs = map reduceGroup (collate fst xs)
    where reduceGroup xs = let (as, bs) = unzip xs in
                             (the as, agg bs)
          the xs | allEq xs = head xs
                 | otherwise= error "'the' applied to nonconstant list"

onCorresponding :: Ord a => ([b]->c) -> [(a,b)] -> [c]
onCorresponding agg xs = map reduceGroup (collate fst xs)
    where reduceGroup xs = agg $ map snd xs


dom alist = map fst alist
rng alist = map snd alist

collate proj = groupBy (\x y -> proj x == proj y) . 
               sortBy (\x y -> proj x `compare` proj y)

sortAlist :: [(String, b)] -> [(String, b)]
sortAlist = sortBy (\a b -> fst a `compare` fst b)

