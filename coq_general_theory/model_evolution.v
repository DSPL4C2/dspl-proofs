Require Import Floats.
Require Import Lists.List.
Require Import String.

Load ADDfloats.
Load formula.

Inductive RDG {Asset : Type} : Type :=
| RDG_leaf (s : string) (ass : Asset)
| RDG_cons (s : string) (ass : Asset) (deps : list RDG).

Definition deps {Asset : Type} (rdg : @RDG Asset) : list RDG :=
  match rdg with
  | RDG_leaf s a => nil
  | RDG_cons s a deps => deps
  end.

Definition asset {Asset : Type} (rdg : @RDG Asset) : Asset :=
  match rdg with
  | RDG_leaf s a => a
  | RDG_cons s a deps => a
  end.

Definition rdgName {Asset : Type} (rdg : @RDG Asset) : string :=
  match rdg with
  | RDG_leaf s a => s
  | RDG_cons s a deps => s
  end.

Inductive Evolution : Type :=
  | ID
  | Message
  | PC
  | AddFeature
  | SubsequentModelEvol
  | RemoveFeature.

Fixpoint functionRecursionAux {Asset T1 T2 : Type} (f1 : (@RDG Asset) -> T1)
  (f2 : T1 -> (list T2) -> T2) (r : @RDG Asset) : T2 :=
  match r with
  | RDG_leaf s ass => f2 (f1 r) nil
  | RDG_cons s ass deps => f2 (f1 r) (map (functionRecursionAux f1 f2) deps)
  end.

Class Analysis (analysis : Type) {Asset : Type} : Type :=
{
  modelChecking : Asset -> RatExpr;
  featureOperation (r : @RDG Asset) : (string * RatExpr) :=
    match r with
    | RDG_leaf s ass => (s , modelChecking ass)
    | RDG_cons s ass deps => (s , modelChecking ass)
    end;
  familyOperation : (string * RatExpr) -> 
    list (string * (ADD float)) -> (string * (ADD float));
  partialFeatureFamilyStep (r : RDG)
    (l : list (string * (ADD float))) : (string * (ADD float)) := 
    familyOperation (featureOperation r) l;
  featureFamily (r : RDG) : (string * (ADD float)) :=
    functionRecursionAux featureOperation familyOperation r
}.

Class Model (model : Type) {Asset : Type} : Type :=
{
(*------------------------------Functions-------------------------------------------*)

  buildRDG : model -> (@RDG Asset);
  evolutionRDG : (@RDG Asset) -> ((@RDG Asset) -> Evolution) -> (@RDG Asset);
  AddedRDG : (@RDG Asset) -> ((@RDG Asset)-> Evolution) -> (@RDG Asset);
  ADDdepsRmvCase : (@RDG Asset) -> ((@RDG Asset) -> Evolution) ->
    list (string * (ADD float)) -> list (string * (ADD float));

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
  deps (evolutionRDG rdg delta) = map (fun r : RDG => evolutionRDG r delta) (deps rdg);

  (*Axiom that describe the behaviour of a rdg evolution that the evolution case is
  the SubsequentModelEvol case*)
  subsequentModelAxiom : forall (r : RDG) (delta : RDG -> Evolution),
  delta r = SubsequentModelEvol -> asset r = asset (evolutionRDG r delta) /\
  rdgName r = rdgName (evolutionRDG r delta)
}.

Check @featureFamily.

(*Axiom that describe the behaviour of a rdg evolution that the evolution case is
the RemoveFeature case*)

Axiom RemoveFeatureAxiom : forall (model Asset analysis: Type)
  `{@Analysis analysis Asset} `{@Model model Asset}, forall (r : RDG)
  (delta : RDG -> Evolution), delta r = RemoveFeature -> 
  ADDdepsRmvCase r delta (map (fun rdg : RDG => featureFamily
  (evolutionRDG rdg delta)) (deps r)) =
  map featureFamily (deps (evolutionRDG r delta)).

Theorem commutativePhiEvolution {Asset model analysis: Type}
  `{@Analysis analysis Asset} `{@Model model Asset} :
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
  rewrite H'. apply commutativeDepsEvolution in H1.
  rewrite H1. reflexivity.
Qed.