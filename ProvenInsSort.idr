module ProvenInsSort

import Data.So
import Sorted
import Permutation
import Forall


tailIsSorted : {f : a -> a -> Type} -> {to : TotalOrder a f} -> (prf : f x y) -> 
    Dec (IsSorted to (y :: xs)) -> Dec (IsSorted to (x :: (y :: xs)))
tailIsSorted {x} prf (Yes prfTail) = Yes $ SortCons x prf prfTail
tailIsSorted prf (No contra) = No $ notSortedTailNotSorted contra

total isSorted : (to : TotalOrder a f) -> (l : List a) -> Dec (IsSorted to l)
isSorted (OrderFn t connex)  [] = Yes SortNil
isSorted (OrderFn t connex)  (x :: []) = Yes (SortOne x)
isSorted {f} (OrderFn t connex) (x :: (y :: xs)) = 
    case (connex x y) of
        (One prf contra) => tailIsSorted prf (isSorted _ _)
        (Both prf ignore) => tailIsSorted prf (isSorted _ _)
        (TheOther prf contra) => No (notSortedHeadNotSorted contra)

total proveInsertion : (to : TotalOrder a f) -> (permPrf : Permutation (x :: ys) insertResult) -> (resultSortPrf : IsSorted to insertResult) -> (subSortPrf : IsSorted to (y :: ys)) -> (prf : f y x) -> (result : List a ** (Permutation (x :: (y :: ys)) result, IsSorted to result))
proveInsertion {insertResult = []} {x} {y} to permPrf resultSortPrf subSortPrf prf = absurd $ permEmptyNotEmptyAbsurd permPrf
proveInsertion {insertResult = r :: rs} {x} {y} to permPrf resultSortPrf subSortPrf prf =
    let yLTys = lteForAllWhenSorted subSortPrf in
        let yLTxys = (And {x = x} prf yLTys) in
            let (And keyPrf ignore) = forallPerm yLTxys permPrf in
                (y :: r :: rs ** (permInsertHead permPrf, (SortCons y keyPrf resultSortPrf)))

total insSortInsert : (to : TotalOrder a f) -> (x : a) -> (subSort : List a) ->  
    (subSortPrf : IsSorted to subSort) ->
    (result : List a ** (Permutation (x :: subSort) result, IsSorted to result))
insSortInsert too x [] SortNil = ([x] ** (PSame, SortOne x))
insSortInsert (OrderFn trans connex) x (y :: ys) subSortPrf = 
    case (connex x y) of
      (One prf contra) => (x :: y :: ys ** (PSame, (SortCons x prf subSortPrf)))
      (Both prf ignore) =>  (x :: y :: ys  ** (PSame, (SortCons x prf subSortPrf)))
      (TheOther prf contra) => let (result ** (permPrf, resultSortPrf)) = insSortInsert (OrderFn trans connex) x ys (sortedHasSortedTail subSortPrf) in 
        proveInsertion (OrderFn trans connex) permPrf resultSortPrf subSortPrf prf

total insSortProven : (to :TotalOrder a f) -> (input : List a) -> (result : List a ** (Permutation input result, IsSorted to result))
insSortProven to [] = ([] ** (PSame, SortNil))
insSortProven to (x :: xs) = let (subSort ** (permPrf, srtPrf)) = insSortProven to xs in
    let (resultList ** (resultPrf,resultSrtPrf)) = insSortInsert to x subSort srtPrf in
        let helper = permuteHead {x = x} permPrf in
          (resultList ** ((PTrans helper resultPrf),resultSrtPrf))

