module Sorted

import Forall
import Data.So

%access public export

data OneOrBoth : p -> q -> Type where
    One : p -> (q -> Void) -> OneOrBoth p q
    TheOther : q -> (p -> Void) -> OneOrBoth p q
    Both : p -> q -> OneOrBoth p q

syntax owoto [oneorbothtest] "of" one {prf} "=>" [onecase] theother {prf} {contra} "=>" [othercase] = 
    case oneorbothtest of
        (One prf contra) => onecase
        (Both prf prf2) => onecase
        (TheOther prf contra) => othercase

data TotalOrder : (a : Type) -> (f : a -> a -> Type) -> Type where
    OrderFn : {a : Type} -> {f : a -> a -> Type } -> 
        (transitive : (x :a) -> (y : a) -> (z : a) -> f x y -> f y z -> f x z) ->
        -- (antisym : (f x y) -> (f y x) -> x = y) ->
        (connex : ((x : a) -> (y : a) -> OneOrBoth (f x y) (f y x))) ->
            TotalOrder a f
           
data IsSorted : (to : TotalOrder a f) -> List a -> Type where
    SortNil : IsSorted to []
    SortOne : (x : a) -> IsSorted to [x]
    SortCons : {to : TotalOrder a f} -> (x : a) -> f x y -> IsSorted to (y :: ys) -> IsSorted to (x :: y :: ys) 

--properties of sorted things

total notSortedTailNotSorted : (contra : (IsSorted to (y :: xs) -> Void)) -> IsSorted to (x :: y :: xs) -> Void
notSortedTailNotSorted contra (SortCons head prf rem) = contra rem

total notSortedHeadNotSorted : {f : a -> a -> Type } -> {to : TotalOrder a f} -> (contra : f x y -> Void) -> IsSorted to (x :: (y :: xs)) -> Void
notSortedHeadNotSorted contra (SortCons head prf rem) = contra prf

total sortedHasSortedTail : {to : TotalOrder a f} -> IsSorted to (x :: xs) -> IsSorted to xs
sortedHasSortedTail (SortOne x) = SortNil
sortedHasSortedTail (SortCons x lte rem) = rem

totalOrderTransitiveOverSort : (to : TotalOrder a f) -> f x y -> (recur : Forall (f y) ys) -> Forall (f x) (ys)
totalOrderTransitiveOverSort (OrderFn transitive connex) lte recur = forAllTransitiveBinaryRel transitive lte recur

total lteForAllWhenSorted : {a : Type} -> {f : a -> a -> Type} -> {to : TotalOrder a f} -> IsSorted to (x :: xs) -> Forall (f x) xs
lteForAllWhenSorted (SortOne x) = ForNone
lteForAllWhenSorted {to} (SortCons x lte rem) = let recur = (lteForAllWhenSorted rem) in
    (And lte $ totalOrderTransitiveOverSort to lte recur)

--Total order over Integer: important functions not actually total. Fast and loose reasoning is morally correct
data LTEInt : (x : Integer) -> (y : Integer) -> Type where
    LTEI : So (x <= y) -> LTEInt x y

total soNotSoAbsurd : So a -> So (not a) -> Void
soNotSoAbsurd Oh s = absurd s

total lteAbsurd : So (not (x <= y)) -> LTEInt x y -> Void
lteAbsurd so (LTEI so2) = soNotSoAbsurd so2 so

intLTEConnex : (x : Integer) -> (y : Integer) -> OneOrBoth (LTEInt x y) (LTEInt y x) 
intLTEConnex x y = assert_total (case (choose (x <= y), choose (y <= x)) of
                        (Left l1, Left l2) => Both (LTEI l1) (LTEI l2)
                        (Left l1, Right r2) => One (LTEI l1) (lteAbsurd r2)
                        (Right r1, Left l2) => TheOther (LTEI l2) (lteAbsurd r1))

intTrans : (x : Integer) -> (y : Integer) -> (z : Integer) -> LTEInt x y -> LTEInt y z -> LTEInt x z
intTrans x y z a b = assert_total (case (choose (x <= z)) of --this can only go one way
                                (Left l) => LTEI l)
        


intTotalOrd : TotalOrder Integer LTEInt
intTotalOrd = OrderFn intTrans intLTEConnex