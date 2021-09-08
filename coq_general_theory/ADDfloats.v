Require Import Floats.

Load add.

(*Defining Operations for ADD float*)

Definition plus_add (f g : ADD float) : ADD float :=
  (fun v : variables => add (f v) (g v)).

Definition sub_add (f g : ADD float) : ADD float :=
  (fun v : variables => sub (f v) (g v)).

Definition mult_add (f g : ADD float) : ADD float :=
  (fun v : variables => mul (f v) (g v)).

Definition div_add (f g : ADD float) : ADD float :=
  (fun v : variables => div (f v) (g v)).

Definition opp_add (f : ADD float) : ADD float :=
  (fun v : variables => opp (f v)).