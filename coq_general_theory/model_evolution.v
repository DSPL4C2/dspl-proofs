Require Import Floats.
Require Import Lists.List.
Require Import String.

Load ADDfloats.
Load formula.

Class Asset (asset : Type) : Type :=
{
  familyOperation : (string * RatExpr) -> 
    list (string * (ADD float)) -> (string * (ADD float))
}.

Inductive RDG {asset : Type} `{Asset asset} : Type :=
| RDG_leaf (s : string) (ass : asset)
| RDG_cons (s : string) (ass : asset) (deps : list RDG).

Definition deps {asset : Type} `{Asset asset} (rdg : RDG) : list RDG :=
  match rdg with
  | RDG_leaf s a => nil
  | RDG_cons s a deps => deps
  end.

Inductive Evolution : Type :=
  | ID
  | Message
  | PC
  | AddFeature
  | SubsequentModelEvol
  | RemoveFeature.

Class Model (model : Type) {asset : Type} `{Asset asset} : Type :=
{
(*------------------------------Functions-------------------------------------------*)

  buildRDG : model -> RDG;
  featureOperation : RDG -> (string * RatExpr);
  evolutionRDG : RDG -> (RDG -> Evolution) -> RDG;
  AddedRDG : RDG -> (RDG -> Evolution) -> RDG;
  ADDdepsRmvCase : RDG -> (RDG -> Evolution) -> list (string * (ADD float)) ->
    list (string * (ADD float));

(*------------------------------Axioms----------------------------------------------*)

  (*Axiom that describe the behaviour of the dependents of a rdg evolution that
  the evolution case is the addiction of a feature*)
  depsAddEvolution :  forall (rdg : RDG) (delta : RDG -> Evolution), 
  delta rdg = AddFeature -> exists (r : RDG) (lr : list RDG),
  deps (evolutionRDG rdg delta) = r :: lr /\ r = AddedRDG rdg delta /\
  lr = map (fun r : RDG => evolutionRDG r delta) (deps rdg);

  (*Axiom that describe the behaviour of a rdg evolution that the evolution case is
  the ID case*)
  partialFeatureFamilyStepIDEvolution : forall (rdg : RDG)
  (delta : RDG -> Evolution), delta rdg = ID -> evolutionRDG rdg delta = rdg;

  (*Axiom that describe the preservation of the structure of the RDG in models that
  the evolution don't change the RDG structure*)
  commutativeDepsEvolution : forall (rdg : RDG) (delta : RDG -> Evolution) ,
  delta rdg <> AddFeature /\ delta rdg <> RemoveFeature ->
  deps (evolutionRDG rdg delta) = map (fun r : RDG => evolutionRDG r delta) (deps rdg)
}.

Fixpoint featureFamily {asset model : Type} `{Asset asset} `{Model model}
  (r : RDG) : (string * (ADD float)) :=
  match r with
  | RDG_leaf s ass => familyOperation (featureOperation r) nil
  | RDG_cons s ass deps =>
      familyOperation (featureOperation r) (map featureFamily deps)
  end.

Definition partialFeatureFamilyStep {asset model : Type} `{Asset asset} `{Model model}
  (r : RDG) (l : list (string * (ADD float))) : (string * (ADD float)) := 
  familyOperation (featureOperation r) l.

(*Axiom that describe the behaviour of a rdg evolution that the evolution case is
the SubsequentModelEvol case*)

Axiom subsequentModelAxiom : forall (model asset: Type) `{Asset asset} 
  `{Model model}, forall (r : RDG) (delta : RDG -> Evolution)
  (l : list (string * (ADD float))), delta r = SubsequentModelEvol -> 
  partialFeatureFamilyStep r l = partialFeatureFamilyStep (evolutionRDG r delta) l.

(*Axiom that describe the behaviour of a rdg evolution that the evolution case is
the RemoveFeature case*)

Axiom RemoveFeatureAxiom : forall (model asset: Type) `{Asset asset} 
  `{Model model}, forall (r : RDG) (delta : RDG -> Evolution),
  delta r = RemoveFeature -> 
  ADDdepsRmvCase r delta (map (fun rdg : RDG => featureFamily (evolutionRDG rdg delta))
  (deps r)) = map featureFamily (deps (evolutionRDG r delta)).

Theorem commutativePhiEvolution : forall (model asset: Type) `{Asset asset} `{Model model},
  forall (rdg : RDG) (delta : RDG -> Evolution) , delta rdg <> AddFeature /\
  delta rdg <> RemoveFeature ->
   map (fun r : RDG => featureFamily (evolutionRDG r delta)) (deps rdg) = 
   map featureFamily (deps (evolutionRDG rdg delta)).
Proof.
  intros. assert (H' : forall (l : list RDG) (d : RDG -> Evolution),
  map (fun r : RDG => featureFamily (evolutionRDG r d)) l = map featureFamily (map 
  (fun r : RDG => evolutionRDG r d) l)).
  { induction l.
    - intros. reflexivity.
    - intros. simpl. rewrite IHl. reflexivity. }
  rewrite H'. apply commutativeDepsEvolution in H2.
  rewrite H2. reflexivity.
Qed.