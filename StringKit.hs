module StringKit where

rpad :: Int -> String -> String
rpad w str = str ++ (spaces (w - length str))

spaces n =  replicate n ' '
