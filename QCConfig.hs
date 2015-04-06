module QCConfig where

import Test.QuickCheck
import NumKit

-- sqrtSizeSmall = Config {configMaxTest = 100,
--                         configMaxFail = 100,
--                         configSize = (\x -> intSqrt x),
--                         configEvery = (\ _ _ -> "")
--                        }

-- medium = Config {configMaxTest = 1000,
--                  configMaxFail = 1000,
--                  configSize = (\x -> 3 + x `div` 2),
--                  configEvery = (\ _ _ -> "")
--                 }

-- logSizeSmall = Config {configMaxTest = 100,
--                   configMaxFail = 100,
--                   configSize = (\x -> (floor . log . (+1) . fromIntegral) x),
--                   configEvery = (\ _ _ -> "")
--                  }
-- logSizeMed = Config {configMaxTest = 1000,
--                   configMaxFail = 1000,
--                   configSize = (\x -> (floor . log . (+1) . fromIntegral) x),
--                   configEvery = (\ _ _ -> "")
--                  }
-- logSize = Config {configMaxTest = 10000,
--                   configMaxFail = 10000,
--                   configSize = (\x -> (floor . log . (+1) . fromIntegral) x),
--                   configEvery = (\ _ _ -> "")
--                  }

