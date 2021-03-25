Record CompositionalThing {PC X : Type} : Type := Composition
{ E : nat -> X
; top : nat
; dependents : nat -> list (PC * nat)
}.