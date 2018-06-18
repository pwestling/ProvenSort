module Forall

%access public export

data Forall : {ty : Type} -> (a -> ty) -> List a -> Type where
    ForNone : Forall p []
    And : (p x) -> Forall p l -> Forall p (x :: l)

-- f x y, f y z 

total forAllTrans : (f : ((x : a) -> p x -> q x)) -> Forall p zs -> Forall q zs
forAllTrans {zs = []} f ForNone = ForNone
forAllTrans {zs = (x :: l)} f (And y z) = And (f x y) (forAllTrans f z)

fn : {f : a -> a -> Type} -> (lte : f x y) -> (trans : (x : a) -> (y : a) -> (z : a) -> f x y -> f y z -> f x z) -> (z : a) -> f y z -> f x z
fn {x} {y} lte trans z ltY = (trans x y z lte ltY)

total forAllTransitiveBinaryRel : {f : a -> a -> Type} -> (trans : (x : a) -> (y : a) -> (z : a) -> f x y -> f y z -> f x z) -> (lte : f x y) -> Forall (f y) zs -> Forall (f x) zs
forAllTransitiveBinaryRel trans lte fa = forAllTrans (fn lte trans) fa 
      
total forAllAppendBack : Forall p (xs ++ ys) -> Forall p ys
forAllAppendBack {xs = []} {ys = ys} fa = fa
forAllAppendBack {xs = (x :: xs)} {ys = ys} (And y z) = forAllAppendBack z

total forAllAppendFront : {xs : List a} -> {ys : List a} -> Forall p (xs ++ ys) -> Forall p xs
forAllAppendFront {xs = []} {ys = ys} fa = ForNone
forAllAppendFront {xs = (x :: gs)} {ys = ys} (And prf rem) with (forAllAppendFront rem)
    | recur = (And prf recur)

total forAllSplit : Forall p (xs ++ ys) -> (Forall p xs, Forall p ys)
forAllSplit fa = (forAllAppendFront fa, forAllAppendBack fa)

total forAllAppend : Forall p xs -> Forall p ys -> Forall p (xs ++ ys)
forAllAppend ForNone y = y
forAllAppend (And z w) y = let recur = (forAllAppend w y) in (And z recur)



