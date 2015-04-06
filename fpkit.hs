module FPKit where

import Maybe (fromJust, isJust)

{- FP utilities -}

cross f g (x,y) = (f x, g y)

onRight f = cross id f
onLeft f = cross f id

($>) x f = f x

image x = fromJust . lookup x

maps x = Maybe.isJust . lookup x

onBoth f (a, b) = (f a, f b)

isRight (Right _) = True
isRight (Left _ ) = False

isLeft (Left _) = True
isLeft (Right _ ) = False

errorMToBool = either (const False) (const True) 

-- withErrMsg msg expr = unsafePerformIO $ catch (evaluate expr)
--                         (\e ->
--                              case e of
--                                Control.Exception.ErrorCall str ->
--                                    error $ msg ++ str 
--                                _ -> error msg)
