module Main

import ProvenInsSort
import Sorted


main : IO ()
main = do
    putStr "Insertion Sort: "
    printLn $ insSort intTotalOrd [5,3,1,8,10,4,6]
    pure ()