
module Algorithm.Mergesort where

open import Logic
open import Function
open import Data.Nat
open import Data.List
open import Relation.Equal
open import Relation.Equal.Nat
open import Relation.Equal.List
open import Relation.Order
open import Relation.Order.Nat
open import Relation.Permutation
open import Group.List

merge :
    ∀ {A op len} -> DecidableOrder op ->
    (xs ys : [ A ]) -> {eq : len == (length xs + length ys)} -> [ A ]
merge order [] ys = ys
merge {len = succ len} order (x :: xs) [] {eq} =
    x :: merge {len = len} order xs [] {==desucc eq}
merge {len = succ len} order (x :: xs) (y :: ys) {eq}
    with DecidableOrder.decide order x y
... | orLeft _ = x :: merge {len = len} order xs (y :: ys) {==desucc eq}
... | orRight _ = y :: merge {len = len} order (x :: xs) ys
    {==trans (==desucc eq) (==sym (addSuccReflexive {length xs}))}
merge {len = zero} _ (_ :: _) _ {()}

merge' : ∀ {A op} -> DecidableOrder op -> [ A ] -> [ A ] -> [ A ]
merge' order xs ys = merge {len = length xs + length ys} order xs ys {==refl}

merge-ordered :
    ∀ {A op b len} -> (order : DecidableOrder op) ->
    (xs ys : [ A ]) -> Ordered order b xs -> Ordered order b ys ->
    {eq : len == (length xs + length ys)} ->
    Ordered order b (merge order xs ys {eq})
merge-ordered _ [] _ _ p2 = p2
merge-ordered {len = succ _} order (x :: xs) [] (orderedCons .x p1 p2) _ =
    orderedCons x p1 $ merge-ordered order xs [] p2 orderedNull
merge-ordered {len = succ len} order (x :: xs) (y :: ys)
    (orderedCons .x p1 p2) (orderedCons .y p3 p4)
        with DecidableOrder.decide order x y
... | orLeft x<=y = orderedCons x p1 $
    merge-ordered {len = len} order xs (y :: ys) p2 (orderedCons y x<=y p4)
... | orRight !x<=y = orderedCons y p3 $
    merge-ordered {len = len} order (x :: xs) ys
        (orderedCons x (trichotomy' order !x<=y) p2) p4
merge-ordered {len = zero} _ (_ :: _) _ _ _ {()}

merge-ordered' :
    ∀ {A op b} -> (order : DecidableOrder op) ->
    (xs ys : [ A ]) -> Ordered order b xs -> Ordered order b ys ->
    Ordered order b (merge' order xs ys)
merge-ordered' order xs ys ox oy = merge-ordered order xs ys ox oy

merge-permutation :
    ∀ {A op len} -> (order : DecidableOrder op) ->
    (xs ys : [ A ]) -> {eq : len == (length xs + length ys)} ->
    Permutation (xs ++ ys) (merge order xs ys {eq})
merge-permutation order [] ys = eqPerm ==refl
merge-permutation {len = succ len} order (x :: xs) [] =
    permSkip $ merge-permutation order xs []
merge-permutation {A = A} {len = succ len} order (x :: xs) (y :: ys)
    with DecidableOrder.decide order x y
... | orLeft _ = permSkip $ merge-permutation {len = len} order xs (y :: ys)
... | orRight _ = permTrans (move {xs = x :: xs}) $ permSkip $
    merge-permutation {len = len} order (x :: xs) ys where
    move : {y : A}{xs ys : [ A ]} ->
           Permutation (xs ++ (y :: ys)) (y :: xs ++ ys)
    move {xs = []} = eqPerm ==refl
    move {xs = x :: xs} = permTrans (permSkip (move {xs = xs})) permSwap
merge-permutation {len = zero} _ (_ :: _) _ {()}

merge-permutation' :
    ∀ {A op} -> (order : DecidableOrder op) -> (xs ys : [ A ]) ->
    Permutation (xs ++ ys) (merge' order xs ys)
merge-permutation' order xs ys = merge-permutation order xs ys

mergePair : ∀ {A op} -> DecidableOrder op -> [ [ A ] ] -> [ [ A ] ]
mergePair order [] = []
mergePair order (x :: []) = x :: []
mergePair order (x :: x' :: xs) = merge' order x x' :: mergePair order xs

<=mergePair : ∀ {A op}{order : DecidableOrder op}{l : [ [ A ] ]} ->
              length (mergePair order l) <= length l
<=mergePair {l = []} = <=zero
<=mergePair {l = _ :: []} = <=succ <=zero
<=mergePair {l = _ :: _ :: l} =
    <=succ $ <=trans (<=mergePair {l = l}) <=reflSucc

mergePair-ordered :
    ∀ {A op b} -> (order : DecidableOrder op) -> (l : [ [ A ] ]) ->
    Sequence (Ordered order b) l ->
    Sequence (Ordered order b) (mergePair order l)
mergePair-ordered order [] nullSeq = nullSeq
mergePair-ordered order (x :: []) (consSeq p nullSeq) = consSeq p nullSeq
mergePair-ordered order (x :: x' :: xs) (consSeq p (consSeq p' p'')) =
    consSeq (merge-ordered' order x x' p p') (mergePair-ordered order xs p'')

mergePair-permutation :
    ∀ {A op} -> (order : DecidableOrder op) -> (l : [ [ A ] ]) ->
    Permutation (concat l) (concat (mergePair order l))
mergePair-permutation order [] = permNull
mergePair-permutation order (x :: []) = eqPerm ==refl
mergePair-permutation order (x :: x' :: xs) =
    permTrans (eqPerm (++assoc {a = x}))
    (permAppend (merge-permutation order x x') (mergePair-permutation order xs))

mergeAll : ∀ {A op n} -> DecidableOrder op -> (l : [ [ A ] ]) ->
           {rel : length l <= n} -> [ A ]
mergeAll order [] = []
mergeAll order (x :: []) = x
mergeAll {n = succ n} order (x :: x' :: xs) {<=succ rel} =
    mergeAll {n = n} order (mergePair order (x :: x' :: xs))
    {<=trans (<=succ (<=mergePair {l = xs})) rel}
mergeAll {n = zero} _ (_ :: _) {()}

mergeAll' : ∀ {A op} -> DecidableOrder op -> [ [ A ] ] -> [ A ]
mergeAll' order xs = mergeAll {n = length xs} order xs {<=refl}

mergeAll-ordered :
    ∀ {A op b n} -> (order : DecidableOrder op) -> (l : [ [ A ] ]) ->
    {rel : length l <= n} -> Sequence (Ordered order b) l ->
    Ordered order b (mergeAll order l {rel})
mergeAll-ordered order [] nullSeq = orderedNull
mergeAll-ordered order (x :: []) (consSeq p _) = p
mergeAll-ordered {n = succ n} order (x :: x' :: xs) {<=succ rel} ordseq =
    mergeAll-ordered {n = n} order (mergePair order (x :: x' :: xs))
        (mergePair-ordered order (x :: x' :: xs) ordseq)
mergeAll-ordered {n = zero} _ (_ :: _) {()} _

mergeAll-ordered' :
    ∀ {A op b} -> (order : DecidableOrder op) -> (l : [ [ A ] ]) ->
    Sequence (Ordered order b) l -> Ordered order b (mergeAll' order l)
mergeAll-ordered' order l ordseq =
    mergeAll-ordered {n = length l} order l {<=refl} ordseq

mergeAll-permutation :
    ∀ {A op n} -> (order : DecidableOrder op) -> (l : [ [ A ] ]) ->
    {rel : length l <= n} -> Permutation (concat l) (mergeAll order l {rel})
mergeAll-permutation order [] = permNull
mergeAll-permutation order (x :: []) = eqPerm ++idright
mergeAll-permutation {n = succ n} order (x :: x' :: xs) {<=succ rel} =
    permTrans (mergePair-permutation order (x :: x' :: xs))
        (mergeAll-permutation {n = n} order (mergePair order (x :: x' :: xs)))
mergeAll-permutation {n = zero} _ (_ :: _) {()}

mergeAll-permutation' :
    ∀ {A op} -> (order : DecidableOrder op) -> (l : [ [ A ] ]) ->
    Permutation (concat l) (mergeAll' order l)
mergeAll-permutation' order l =
    mergeAll-permutation {n = length l} order l {<=refl}

mergesort : ∀ {A op} -> DecidableOrder op -> [ A ] -> [ A ]
mergesort order xs = mergeAll' order $ map (flip _::_ []) xs

mergesort-ordered :
    ∀ {A op b} -> (order : DecidableOrder op) -> (l : [ A ]) ->
    Sequence (op b) l -> Ordered order b (mergesort order l)
mergesort-ordered {A} {op} {b} order l ps =
    mergeAll-ordered' order (map (flip _::_ []) l) (p l ps) where
    p : (l : [ A ]) -> Sequence (op b) l ->
        Sequence (Ordered order b) (map (flip _::_ []) l)
    p [] nullSeq = nullSeq
    p (x :: xs) (consSeq p1 p2) =
        consSeq (orderedCons x p1 orderedNull) (p xs p2)

mergesort-permutation :
    ∀ {A op} -> (order : DecidableOrder op) -> (l : [ A ]) ->
    Permutation l (mergesort order l)
mergesort-permutation order l =
    permTrans (eqPerm p) (mergeAll-permutation' order (map (flip _::_ []) l))
    where
    p : ∀ {l} -> l == concat (map (flip _::_ []) l)
    p {[]} = ==refl
    p {x :: xs} = ==cons ==refl $ p {xs}

