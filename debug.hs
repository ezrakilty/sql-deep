module Debug where

import Control.Monad.Error
import Foreign (unsafePerformIO)

debugFlag =                        -- enable/disable debugging messages
    False

contract p x = if p x then x else error "assertion failed"

assert x e = if x then e else error "assertion failed"

instance Error () where
    noMsg = ()
    strMsg _ = ()

-- Debugging utilities

breakFlag x = x     -- a breakpoint

debug str = seq(if debugFlag then Foreign.unsafePerformIO$ putStrLn str else ())
