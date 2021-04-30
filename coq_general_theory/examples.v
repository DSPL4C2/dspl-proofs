Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.Init.Wf.
Require Import Coq.Program.Equality.
Require Import Floats.

Load compositionalThing.

Class Property (Proper : Type) : Type :=
{
  emptyProperty : Proper
}.

Class PresenceCondition (PC : Type) : Type :=
{
}.

Inductive SQLOrNot : Type :=
  | SQL
  | NotSQL.

Instance PCSQL : PresenceCondition SQLOrNot := {}.

Definition conf : Type := SQLOrNot -> bool.

Instance Reliability : Property float := 
{
  emptyProperty := 1
}.

Inductive VariableStructure {X PC: Type} `{PresenceCondition PC}: Type :=
  | Base (x : X)
  | Choice (pc : PC) (s1 s2 : VariableStructure).

Definition AnnotativeExpression : Type := @VariableStructure float SQLOrNot PCSQL.

Definition partialECT : Type := AnnotativeExpression -> AnnotativeExpression -> AnnotativeExpression.

Inductive SigmaRelation : AnnotativeExpression -> conf -> float -> Prop :=
  | BaseCaseSig (p : float) (c:  conf) : SigmaRelation (Base p) c p
  | Choice1Sig (ae1 ae2 : AnnotativeExpression) (p : float) (pc : SQLOrNot) (c : conf) 
      (H1 : c pc = true) (H2 : SigmaRelation ae1 c p) : SigmaRelation (Choice pc ae1 ae2) c p
  | Choice2Sig (ae1 ae2 : AnnotativeExpression) (p : float) (pc : SQLOrNot) (c : conf) 
      (H1 : c pc = false) (H2 : SigmaRelation ae2 c p) : SigmaRelation (Choice pc ae1 ae2) c p.

Definition CompositionalExpression : Type :=
  @CompositionalThing SQLOrNot AnnotativeExpression.

Fixpoint partialExpressionComposition (a1 a2 : AnnotativeExpression) : AnnotativeExpression :=
  match a1, a2 with
  | Base x1 , Base x2 => Base (x1 * x2)%float
  | Choice pc a3 a4 , Base x2 => Choice pc (partialExpressionComposition a3 a2) (partialExpressionComposition a4 a2)
  | _ , _ => Base 0%float
  end.

Inductive SigmaCompRelation_aux : CompositionalExpression -> AnnotativeExpression -> list (SQLOrNot * nat) -> conf -> partialECT -> float -> Prop :=
  | NilListSig (ce : CompositionalExpression) (ae : AnnotativeExpression) (c : conf) (proper : float)
      (partialEC : partialECT) (H1 : SigmaRelation ae c proper) : 
      SigmaCompRelation_aux ce ae nil c partialEC proper
  | TruePCCaseSig (ce : CompositionalExpression) (ae : AnnotativeExpression) (t : list (SQLOrNot * nat)) (c : conf) (proper1 proper2 : float)
      (h : (SQLOrNot * nat)) (partialEC : partialECT) (H1 : c (fst h) = true)
      (H2 : SigmaCompRelation_aux ce (ce.(E) (snd h)) (ce.(dependents) (snd h)) c partialEC proper2)
      (H3 : SigmaCompRelation_aux ce (partialEC ae (Base proper2)) t c partialEC proper1) :
      SigmaCompRelation_aux ce ae (h :: t) c partialEC proper1
  | FalsePCCaseSig (ce : CompositionalExpression) (ae : AnnotativeExpression) (t : list (SQLOrNot * nat)) (c : conf) (proper : float)
      (h : (SQLOrNot * nat)) (partialEC : partialECT) (H1 : c (fst h) = false)
      (H2 : SigmaCompRelation_aux ce (partialEC ae (Base emptyProperty)) t c partialEC proper) : 
       SigmaCompRelation_aux ce ae (h :: t) c partialEC proper.

Definition SigmaCompRelation (ce : CompositionalExpression) (c : conf) (p: float) (partialEC : partialECT) : Prop :=
  SigmaCompRelation_aux ce (ce.(E) ce.(top)) (ce.(dependents) ce.(top)) c partialEC p.

Definition example := 
{| E := fun (x : nat) => match x with
                         | 0 => Choice SQL (Base (0.99 * 0.99 * 0.99)%float) (Base (0.99 * 0.99 * 0.99)%float)
                         | 1 => Base (0.99)%float
                         | _ => Base (0.99)%float
                         end;
  top := 0;
  dependents := fun (x : nat) => match x with
                                 | 0 => (SQL,1)::((NotSQL,2)::nil)
                                 | _ => nil
                                 end
|}.

Definition exampleConf : conf := fun x => match x with
                                          | SQL => true
                                          | NotSQL => false
                                          end.

Theorem exampleTheorem : SigmaCompRelation example exampleConf (0.99 * 0.99 * 0.99 * 0.99) partialExpressionComposition.
Proof.
  unfold SigmaCompRelation. simpl. apply (TruePCCaseSig _ _ _ _ _ 0.99).
  - reflexivity.
  - simpl. constructor. constructor.
  - apply FalsePCCaseSig.
    + reflexivity.
    + simpl. constructor. constructor. reflexivity. constructor.
Qed.

