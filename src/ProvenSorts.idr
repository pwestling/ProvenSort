module Main

import ProvenInsSort
import Sorted

myEfficientLookup : (UComparator a n) -> Vect n a


main : IO ()
main = do
    putStr "Insertion Sort: "
    printLn $ insSort intTotalOrd [5,3,1,8,10,4,6]
    pure ()