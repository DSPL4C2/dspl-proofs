Definition variables : Type := list bool.

Definition ADD (T : Type) : Type := variables -> T.

Definition constant {T : Type} (t : T) : ADD T := fun (v : variables) => t.

Definition apply {T : Type} (f g : ADD T) (op : T -> T -> T) : ADD T :=
  fun (v : variables) => op (f v) (g v).

Definition unary_apply {T : Type} (f : ADD T) (op : T -> T) : ADD T :=
  fun (v : variables) => op (f v).

Definition ite {T : Type} (test : ADD bool) (f g : ADD T) : ADD T :=
  fun (v : variables) => if (test v) then (f v)
                                     else (g v).