module Permutation

import Forall

%access public export

data Permutation : (x : List a) -> (y : List a) -> Type where
    PSame : Permutation x x
    PInsert : (x : a) -> (xs : List a) -> (ys : List a) -> (ws : List a) -> (zs : List a) -> 
        Permutation (xs ++ ys) (ws ++ zs) -> Permutation (xs ++ (x :: ys)) (ws ++ (x :: zs))
    PTrans : Permutation x y -> Permutation y z -> Permutation x z

total permuteRefl : Permutation x y -> Permutation y x
permuteRefl PSame = PSame
permuteRefl (PInsert x xs ys ws zs prf) = let recur = permuteRefl prf in
    (PInsert x ws zs xs ys recur)
permuteRefl (PTrans x y) = PTrans (permuteRefl y) (permuteRefl x)

total permuteHead : Permutation y z -> Permutation (x :: y) (x :: z)
permuteHead PSame = PSame
permuteHead {x} wholePrf@(PInsert k xs ys ws zs prf) = (PInsert x [] (xs ++ (k :: ys)) [] (ws ++ (k :: zs)) wholePrf)
permuteHead (PTrans p1 p2) = PTrans (permuteHead p1) (permuteHead p2)

total permEq : (x = y) -> Permutation x z -> Permutation y z
permEq Refl x = x

total permEmpty : Permutation [] x -> x = []
permEmpty PSame = Refl
permEmpty (PTrans p1 p2) with (permEmpty p1)
    | Refl = permEmpty p2
permEmpty (PInsert k [] [] [] [] perm) impossible 

total permInsertHead : Permutation (x :: ys) (r :: rs) -> Permutation (x :: y :: ys) (y :: r :: rs)
permInsertHead {x} {ys} {r} {rs} {y} p = (PInsert y [x] ys [] (r :: rs) p)

total permEmptyNotEmptyAbsurd : Permutation (x :: ys) [] -> Void
permEmptyNotEmptyAbsurd x with (permEmpty (permuteRefl x))
    | contra = lemma_val_not_nil contra
    

total forallPerm : {xs : List a} -> {ys : List a} -> Forall p xs -> Permutation xs ys -> Forall p ys
forallPerm fax PSame = fax
forallPerm fax (PTrans x z) = forallPerm (forallPerm fax x) z
forallPerm {xs = (xs ++ x :: ys)} {ys = (ws ++ x :: zs)} fax (PInsert x xs ys ws zs subPerm) with (forAllSplit fax) 
    | (faf, (And prfX fab)) = 
        let append = forAllAppend faf fab in
            let trans = forallPerm append subPerm in
                let (fstsplit, sndsplit) = forAllSplit trans in
                    let attached = (And prfX sndsplit) in
                        forAllAppend fstsplit attached

