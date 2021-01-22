Class Property (X : Type) : Type :=
{}.

Class Product (X : Type) {Y : Type} `{Property Y} : Type :=
{
  alpha : X -> Y
}.

Class PresenceCondition (X : Type) : Type :=
{}.

Inductive VariableStructure (X Y : Type) `{PresenceCondition Y}: Type :=
  | Base (x : X)
  | Choice (pc : Y) (s1 s2 : VariableStructure X Y).

Definition AnnotativeModel {X Y: Type} `{Product X} `{PresenceCondition Y}: Type := VariableStructure X Y.

Definition AnnotativeExpression {X Y: Type} `{Property X} `{PresenceCondition Y}: Type := VariableStructure X Y.

Inductive PiRelation {Prod PC : Type} `{Product Prod} `{PresenceCondition PC} : AnnotativeModel -> (PC -> bool) -> Prod -> Prop :=
  | BaseCasePi (p : Prod) (c:  PC -> bool) : PiRelation (Base Prod PC p) c p
  | Choice1Pi (am1 am2 : AnnotativeModel) (p : Prod) (pc : PC) (c : PC -> bool) 
      (H1 : c pc = true) (H2 : PiRelation am1 c p) : PiRelation (Choice Prod PC pc am1 am2) c p
  | Choice2Pi (am1 am2 : AnnotativeModel) (p : Prod) (pc : PC) (c : PC -> bool) 
      (H1 : c pc = false) (H2 : PiRelation am2 c p) : PiRelation (Choice Prod PC pc am1 am2) c p.

Inductive SigmaRelation {Proper PC : Type} `{Property Proper} `{PresenceCondition PC} : AnnotativeExpression -> (PC -> bool) -> Proper -> Prop :=
  | BaseCaseSig (p : Proper) (c:  PC -> bool) : SigmaRelation (Base Proper PC p) c p
  | Choice1Sig (ae1 ae2 : AnnotativeExpression) (p : Proper) (pc : PC) (c : PC -> bool) 
      (H1 : c pc = true) (H2 : SigmaRelation ae1 c p) : SigmaRelation (Choice Proper PC pc ae1 ae2) c p
  | Choice2Sig (ae1 ae2 : AnnotativeExpression) (p : Proper) (pc : PC) (c : PC -> bool) 
      (H1 : c pc = false) (H2 : SigmaRelation ae2 c p) : SigmaRelation (Choice Proper PC pc ae1 ae2) c p.

Inductive HatAlphaRelation {Prod Proper PC : Type} {Hp : Property Proper} `{@Product Prod Proper Hp} `{PresenceCondition PC} : AnnotativeModel -> AnnotativeExpression -> Prop :=
  | BaseCase (prod : Prod) (proper : Proper) (H : alpha prod = proper) : 
      HatAlphaRelation (Base Prod PC prod) (Base Proper PC proper)
  | ChoiceCase (am1 am2 : AnnotativeModel) (ae1 ae2 : AnnotativeExpression) (pc : PC) 
      (H1: HatAlphaRelation am1 ae1) (H2: HatAlphaRelation am2 ae2) : 
      HatAlphaRelation (Choice Prod PC pc am1 am2) (Choice Proper PC pc ae1 ae2).

Theorem commutative_product_family_product {Prod Proper PC : Type} `{Hp : Property Proper}
  `{@Product Prod Proper Hp} `{PresenceCondition PC} : forall (am : AnnotativeModel) 
  (ae : AnnotativeExpression)(c : PC -> bool) (prod : Prod) (proper : Proper), 
  HatAlphaRelation am ae -> PiRelation am c prod -> alpha prod = proper -> SigmaRelation ae c proper.
Proof.
  intros. induction H1.
  - inversion H2. subst. constructor.
  - inversion H2. 
    + subst. apply Choice1Sig. auto. apply IHHatAlphaRelation1. apply H9.
    + subst. apply Choice2Sig. auto. apply IHHatAlphaRelation2. apply H9.
Qed.
