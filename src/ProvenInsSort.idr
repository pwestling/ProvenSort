
module ProvenInsSort


import Data.So
import Sorted
import Permutation
import Forall
import Data.Vect
import Data.Nat.Views

%language UniquenessTypes


tailIsSorted : {f : a -> a -> Type} -> {to : TotalOrder a f} -> (prf : f x y) -> 
    Dec (IsSorted to (y :: xs)) -> Dec (IsSorted to (x :: (y :: xs)))
tailIsSorted {x} prf (Yes prfTail) = Yes $ SortCons x prf prfTail
tailIsSorted prf (No contra) = No $ notSortedTailNotSorted contra

export
total isSorted : (to : TotalOrder a f) -> (l : List a) -> Dec (IsSorted to l)
isSorted (OrderFn t connex)  [] = Yes SortNil
isSorted (OrderFn t connex)  (x :: []) = Yes (SortOne x)
isSorted {f} (OrderFn t connex) (x :: (y :: xs)) = 
    owoto (connex x y) of
        one prf => tailIsSorted prf (isSorted _ _)
        theother prf contra => No (notSortedHeadNotSorted contra)

total proveInsertion : {insertResult : List a} -> {y : a} -> (to : TotalOrder a f) -> (permPrf : Permutation (x :: ys) insertResult) -> (resultSortPrf : IsSorted to insertResult) -> (subSortPrf : IsSorted to (y :: ys)) -> (prf : f y x) -> (result : List a ** (Permutation (x :: (y :: ys)) result, IsSorted to result))
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
    owoto (connex x y) of
      one prf => (x :: y :: ys ** (PSame, (SortCons x prf subSortPrf)))
      theother prf contra => let (result ** (permPrf, resultSortPrf)) = insSortInsert (OrderFn trans connex) x ys (sortedHasSortedTail subSortPrf) in 
        proveInsertion (OrderFn trans connex) permPrf resultSortPrf subSortPrf prf

total insSortProven : (to :TotalOrder a f) -> (input : List a) -> (result : List a ** (Permutation input result, IsSorted to result))
insSortProven to [] = ([] ** (PSame, SortNil))
insSortProven to (x :: xs) = let (subSort ** (permPrf, srtPrf)) = insSortProven to xs in
    let (resultList ** (resultPrf,resultSrtPrf)) = insSortInsert to x subSort srtPrf in
        let helper = permuteHead {x = x} permPrf in
          (resultList ** ((permuteTrans helper resultPrf),resultSrtPrf))
export          
total insSort : (to :TotalOrder a f) -> (input : List a) -> List a
insSort to l = fst (insSortProven to l)

NotElem : (x : a) -> Vect n a -> Type 
NotElem x l = Not (Elem x l)

data UniqueVect : Vect n a -> Type where
    UniqueNil : UniqueVect []
    UniqueCons : (x : a) -> (l : UniqueVect v) -> (NotElem x v) -> UniqueVect (x :: v)

notUniqueIfIsElem : (prf : Elem x xs) -> UniqueVect (x :: xs) -> Void
notUniqueIfIsElem prf (UniqueCons x l f) = f prf

notUniqueTailNotUnique : (contra : UniqueVect xs -> Void)  -> UniqueVect (x :: xs) -> Void
notUniqueTailNotUnique contra (UniqueCons x l f) = contra l

total isUnique : DecEq a => (l : Vect n a) -> Dec (UniqueVect l)
isUnique [] = Yes UniqueNil
isUnique (x :: xs) = case (isElem x xs) of
                        (Yes prf) => No (notUniqueIfIsElem prf)
                        (No notElem) => (case (isUnique xs) of
                                             (Yes prf) => Yes $ UniqueCons x prf notElem
                                             (No contra) => No $ (notUniqueTailNotUnique contra))
                                             
isUniqueBool : DecEq a => (l : Vect n a) -> Bool
isUniqueBool l = case isUnique l of
                    (Yes _) => True
                    (No _) => False


toBinary' : (k : Nat) -> List Char
toBinary' k with (halfRec k)
    toBinary' Z | HalfRecZ = ['4']
    toBinary' (n + n) | (HalfRecEven evenRec) = (::) '0' (toBinary' n | evenRec)
    toBinary' (S (n + n)) | (HalfRecOdd oddRec) = (::) '1' (toBinary' n | oddRec)

public export    
data Uni : a -> UniqueType where
    U : a -> Uni a

export
data UComparator : Nat -> a -> UniqueType where
    MkComparator : (allowedUses : Nat) -> (comp : (a -> a -> Bool)) -> UComparator allowedUses a
   
interface EfficientLookup (c : UniqueType) where
    keyType : c ->  Type
    valType : c ->  Type
    size : c ->  Nat
    lookupImpl : (coll : c) -> (UComparator (size coll) (keyType coll)) -> (keyType coll) -> Uni (valType coll)

export
total compareOnce : {n : Nat} -> {a : Type} -> UComparator (S n) a  -> a -> a -> UPair Bool (UComparator n a)
compareOnce (MkComparator (S rem) comp) a1 a2 = (comp a1 a2,  MkComparator rem comp)