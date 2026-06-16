module Hello where

import Numeric.Natural (Natural)

fun :: [Natural] -> Bool
fun x = if not (length x == 1) then False else True

