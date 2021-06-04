Require Import Floats.
Require Import FSets.
Require Import Lists.List.

Load add.
Load zip.
Load all.

Class Asset (asset : Type) : Type :=
{}.

Inductive RDG {asset : Type} `{Asset asset} : Type :=
| RDG_leaf (ass : asset)
| RDG_cons (ass : asset) (deps : list RDG).

Inductive Evolution : Type :=
  | ID
  | Mensage.
(*
  | PC
  | AddFeature
  | RemoveFeature
  | SubsequentModelEvol.*)

Class Model (model : Type) {asset : Type} `{Asset asset} : Type :=
{
  buildRDG : model -> RDG;
  evolutionRDG : RDG -> (RDG -> Evolution) -> RDG;
  phi : RDG -> ADD float;
  phiInd' : RDG -> list (ADD float) -> ADD float;
  AddedModels : model -> (model -> Evolution) -> model;
  RemovedModels : model -> (model -> Evolution) -> model
}.

Definition deps {asset : Type} `{Asset asset} (rdg : RDG) : list RDG :=
  match rdg with
  | RDG_leaf a => nil
  | RDG_cons a deps => deps
  end.

Fixpoint Phi'Aux {model asset :Type} `{Asset asset} `{Model model}
  (rdg : RDG) (delta : RDG -> Evolution) : (ADD float) := 
  match rdg with
  | RDG_leaf a => phi (evolutionRDG rdg delta)
  | RDG_cons a deps => match (delta rdg) with
                       | ID => phi rdg
                       | Message => phiInd' (evolutionRDG rdg delta)
                          (map (fun (x : RDG) => Phi'Aux (x) delta) deps)
                       end
  end.

Definition Phi'Fun {model asset :Type} `{Asset asset} `{Model model}
  (mod : model) (delta : RDG -> Evolution) : ADD float := 
  Phi'Aux (buildRDG mod) delta.

Axiom phiInd'Equivalence : forall (model asset: Type) `{Asset asset} `{Model model},
  forall (rdg : RDG),
  phiInd' rdg (map phi (deps rdg)) = phi rdg.

Axiom phiInd'IDEvolution : forall (model asset: Type) `{Asset asset} `{Model model},
  forall (rdg : RDG) (delta : RDG -> Evolution), delta rdg = ID ->
  evolutionRDG rdg delta = rdg.

(*Axiom depsRDGEvolution : forall (model asset: Type) `{Asset asset} `{Model model},
  forall (rdg : RDG) (delta : RDG -> Evolution) , delta rdg <> AddFeature /\
  delta rdg <> RemoveFeature -> 
  length (deps rdg) = length (deps (evolutionRDG rdg delta)).*)

Axiom depsLengthRDGEvolution : forall (model asset: Type) `{Asset asset} 
  `{Model model}, forall (rdg : RDG) (delta : RDG -> Evolution), 
  length (deps rdg) = length (deps (evolutionRDG rdg delta)).

Definition Phi'AuxDelta {model asset: Type} {H1 : Asset asset} {H2 : Model model}
  (delta : RDG -> Evolution) : RDG -> Prop :=
  (fun (r : RDG) => @Phi'Aux model asset H1 asset H1 H2 r delta = 
  phi (evolutionRDG r delta)).
(*Tentativa de Replicar a hipótese NNode'_case para implementar uma nova
indução para o tipo RDG, já que a indução disponibilizada pelo coq para nested
types é fraca*) (* Tentativa baseada no capitulo 3.8 do livro do Chlipala*)
(*
Theorem RDG_case {model asset: Type} {H1 : Asset asset} {H2 : Model model} :
  forall (a : asset) (lr : list RDG) (delta : RDG -> Evolution),
  (All (Phi'AuxDelta delta) lr )-> 
   (Phi'AuxDelta delta)(RDG_cons a lr).
Proof.
  intros. unfold Phi'AuxDelta in *. destruct lr.
  - simpl. destruct (delta (RDG_cons a nil)) eqn:H'.
    + apply (phiInd'IDEvolution model asset (RDG_cons a nil)) in H'.
      rewrite H'. reflexivity.
    + assert (H'' : phiInd' (evolutionRDG (RDG_cons a nil) delta) 
      (map phi (deps (evolutionRDG (RDG_cons a nil) delta))) = 
      phi (evolutionRDG (RDG_cons a nil) delta)).
      * apply (phiInd'Equivalence model asset).
      * rewrite <- H''.
        assert (H''' : deps (evolutionRDG (RDG_cons a nil) delta) = nil).
        { apply length_zero_iff_nil. 
          assert (L : length (deps (RDG_cons a nil)) = 0). reflexivity.
          rewrite <- L. symmetry. apply (depsLengthRDGEvolution model asset). }
        rewrite H'''. reflexivity.
  - simpl. destruct (delta (RDG_cons a (r::lr))) eqn:H'.
    + apply (phiInd'IDEvolution model asset (RDG_cons a (r :: lr))) in H'.
      rewrite H'. reflexivity.
    +*)

Theorem Phi'EquivalenceAux {model asset :Type} `{Asset asset} `{Model model} :
  forall (rdg : RDG) (delta : RDG -> Evolution),
  Phi'Aux rdg delta = phi (evolutionRDG rdg delta).
Proof.
  intros. apply (well_founded_ind (RDG) (fun r1 r2 : RDG => In r1 (deps r2))
  (fun r : RDG => Phi'Aux r delta = phi (evolutionRDG r delta)) ).


Theorem Phi'Equivalence {model asset :Type} `{Asset asset} `{Model model} :
  forall (m : model) (delta : RDG -> Evolution), 
  Phi'Fun m delta = phi (evolutionRDG (buildRDG m) delta).
Proof.
  intros. unfold Phi'Fun. remember (buildRDG m) as rdg.
  induction rdg.
  - reflexivity.
  - 




Proof.
  intros. unfold Phi'Fun. remember (buildRDG m) as rdg. 
  destruct rdg. simpl. induction deps0.
  - destruct (delta (RDG_cons ass nil)) eqn:H'.
    + apply (phiInd'IDEvolution model asset) in H'.
      rewrite H'. reflexivity.
    + simpl. assert (H'' : phiInd' (evolutionRDG (RDG_cons ass nil) delta) 
      (map phi (deps (evolutionRDG (RDG_cons ass nil) delta))) = 
      phi (evolutionRDG (RDG_cons ass nil) delta)).
      * apply (phiInd'Equivalence model asset).
      * rewrite <- H''. 
        assert (H''' : deps (evolutionRDG (RDG_cons ass nil) delta) = nil).
        { apply length_zero_iff_nil. 
          assert (L : length (deps (RDG_cons ass nil)) = 0). reflexivity.
          rewrite <- L. symmetry. apply (depsLengthRDGEvolution model asset). }
        rewrite H'''. reflexivity.
  -



induction (delta (RDG_cons ass deps0)) eqn:H'.
  - apply (phiInd'IDEvolution model asset) in H'. rewrite H'.
    reflexivity.
  -



