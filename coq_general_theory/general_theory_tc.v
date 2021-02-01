Require Import Ensembles.

Class Property (X : Type) : Type :=
{
  emptyProperty : X
}.

Class Product (X : Type) {Y : Type} `{Property Y} : Type :=
{
  emptyProduct : X;
  alpha : X -> Y
}.

Axiom AlphaEmpty : forall (X Y : Type) `{Property Y} `{Product X}, alpha emptyProduct = emptyProperty.

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

Record CompositionalThing {X PC : Type} `{PresenceCondition PC}: Type := Composition
{ E : nat -> X
; top : nat
; dependents : nat -> list (PC * nat)
}.

Definition CompositionalModel {X Y: Type} `{Product X} {H : PresenceCondition Y} : Type := 
  @CompositionalThing (AnnotativeModel) Y H.

Definition CompositionalExpression {X Y: Type} `{Property X} {H : PresenceCondition Y}: Type :=
  @CompositionalThing (AnnotativeExpression) Y H.

Inductive HatAlphaCompRelation {Prod Proper PC : Type} {Hp : Property Proper} `{@Product Prod Proper Hp} `{PresenceCondition PC} : CompositionalModel -> CompositionalExpression -> Prop :=
  | FMapHa (cm : CompositionalModel) (ce : CompositionalExpression) (H1 : cm.(top) = ce.(top))
      (H2 : forall (n : nat), HatAlphaRelation (cm.(E) n) (ce.(E) n)) (H3 : cm.(dependents) = ce.(dependents)) :
      HatAlphaCompRelation cm ce.

Inductive PiCompRelation_aux {Prod PC : Type} `{Product Prod} `{PresenceCondition PC} : CompositionalModel -> AnnotativeModel -> list (PC * nat) -> (PC -> bool) -> (AnnotativeModel -> AnnotativeModel -> AnnotativeModel) -> Prod -> Prop :=
  | NilListPi (cm : CompositionalModel) (am : AnnotativeModel) (c : PC -> bool) (prod : Prod)
      (partialMC : AnnotativeModel -> AnnotativeModel -> AnnotativeModel) (H1 : PiRelation am c prod) : 
      PiCompRelation_aux cm am nil c partialMC prod
  | TruePCCasePi (cm : CompositionalModel) (am : AnnotativeModel) (t : list (PC * nat)) (c : PC -> bool) (prod1 prod2 : Prod)
      (h : (PC * nat)) (partialMC : AnnotativeModel -> AnnotativeModel -> AnnotativeModel) (H1 : c (fst h) = true)
      (H2 : PiCompRelation_aux cm (cm.(E) (snd h)) (cm.(dependents) (snd h)) c partialMC prod2)
      (H3 : PiCompRelation_aux cm (partialMC am (Base Prod PC prod2)) t c partialMC prod1) :
      PiCompRelation_aux cm am (h :: t) c partialMC prod1
  | FalsePCCasePi (cm : CompositionalModel) (am : AnnotativeModel) (t : list (PC * nat)) (c : PC -> bool) (prod : Prod)
      (h : (PC * nat)) (partialMC : AnnotativeModel -> AnnotativeModel -> AnnotativeModel) (H1 : c (fst h) = false)
      (H2 : PiCompRelation_aux cm (partialMC am (Base Prod PC emptyProduct)) t c partialMC prod) : 
       PiCompRelation_aux cm am (h :: t) c partialMC prod.
      
Inductive SigmaCompRelation_aux {Proper PC : Type} `{Property Proper} `{PresenceCondition PC} : CompositionalExpression -> AnnotativeExpression -> list (PC * nat) -> (PC -> bool) -> (AnnotativeExpression -> AnnotativeExpression -> AnnotativeExpression) -> Proper -> Prop :=
  | NilListSig (ce : CompositionalExpression) (ae : AnnotativeExpression) (c : PC -> bool) (proper : Proper)
      (partialEC : AnnotativeExpression -> AnnotativeExpression -> AnnotativeExpression) (H1 : SigmaRelation ae c proper) : 
      SigmaCompRelation_aux ce ae nil c partialEC proper
  | TruePCCaseSig (ce : CompositionalExpression) (ae : AnnotativeExpression) (t : list (PC * nat)) (c : PC -> bool) (proper1 proper2 : Proper)
      (h : (PC * nat)) (partialEC : AnnotativeExpression -> AnnotativeExpression -> AnnotativeExpression) (H1 : c (fst h) = true)
      (H2 : SigmaCompRelation_aux ce (ce.(E) (snd h)) (ce.(dependents) (snd h)) c partialEC proper2)
      (H3 : SigmaCompRelation_aux ce (partialEC ae (Base Proper PC proper2)) t c partialEC proper1) :
      SigmaCompRelation_aux ce ae (h :: t) c partialEC proper1
  | FalsePCCaseSig (ce : CompositionalExpression) (ae : AnnotativeExpression) (t : list (PC * nat)) (c : PC -> bool) (proper : Proper)
      (h : (PC * nat)) (partialEC : AnnotativeExpression -> AnnotativeExpression -> AnnotativeExpression) (H1 : c (fst h) = false)
      (H2 : SigmaCompRelation_aux ce (partialEC ae (Base Proper PC emptyProperty)) t c partialEC proper) : 
       SigmaCompRelation_aux ce ae (h :: t) c partialEC proper.

Definition PiCompRelation {Prod PC : Type} `{Product Prod} `{PresenceCondition PC} (cm : CompositionalModel) (c : PC -> bool) (p : Prod) (partialMC : AnnotativeModel -> AnnotativeModel -> AnnotativeModel) : Prop :=
  PiCompRelation_aux cm (cm.(E) cm.(top)) (cm.(dependents) cm.(top)) c partialMC p.

Definition SigmaCompRelation {Proper PC : Type} `{Property Proper} `{PresenceCondition PC} (ce : CompositionalExpression) (c : PC -> bool) (p: Proper) (partialEC : AnnotativeExpression -> AnnotativeExpression -> AnnotativeExpression) : Prop :=
  SigmaCompRelation_aux ce (ce.(E) ce.(top)) (ce.(dependents) ce.(top)) c partialEC p.

Theorem aux_commutative_feature_product_product {Prod Proper PC : Type} {Hp : Property Proper}
  `{@Product Prod Proper Hp} `{PresenceCondition PC} : forall (l : list (PC * nat)) (cm : CompositionalModel) 
  (ce : CompositionalExpression) (c : PC -> bool) (prod : Prod) (proper : Proper) (ae : AnnotativeExpression)
  (partialMC : AnnotativeModel -> AnnotativeModel -> AnnotativeModel) (am : AnnotativeModel)
  (partialEC : AnnotativeExpression -> AnnotativeExpression -> AnnotativeExpression),
  ( forall (am1 am2 : AnnotativeModel) (ae1 ae2 : AnnotativeExpression),
    HatAlphaRelation am1 ae1 -> HatAlphaRelation am2 ae2 -> HatAlphaRelation (partialMC am1 am2) (partialEC ae1 ae2)) ->
  HatAlphaCompRelation cm ce -> PiCompRelation_aux cm am l c partialMC prod -> alpha prod = proper ->
  HatAlphaRelation am ae -> SigmaCompRelation_aux ce ae l c partialEC proper.
Proof.
  intros. generalize dependent ae. generalize dependent proper. induction H3.
  - intros. constructor. apply (commutative_product_family_product am _ _ prod);auto.
  - intros. apply (TruePCCaseSig _ _ _ _ _ (alpha prod2)).
    + auto.
    + inversion H2. rewrite <- H8. apply IHPiCompRelation_aux1;try(auto).
    + apply IHPiCompRelation_aux2;try(auto). apply H1.
      * auto.
      * constructor. reflexivity.
  - intros. constructor. auto. apply IHPiCompRelation_aux;try(auto).
    + apply H1. auto. constructor. apply (AlphaEmpty Prod Proper).
Qed.

Theorem commutative_feature_product_product {Prod Proper PC : Type} {Hp : Property Proper}
  `{@Product Prod Proper Hp} `{PresenceCondition PC} : forall (cm : CompositionalModel) 
  (ce : CompositionalExpression) (c : PC -> bool) (prod : Prod) (proper : Proper)
  (partialMC : AnnotativeModel -> AnnotativeModel -> AnnotativeModel)
  (partialEC : AnnotativeExpression -> AnnotativeExpression -> AnnotativeExpression),
  ( forall (am1 am2 : AnnotativeModel) (ae1 ae2 : AnnotativeExpression),
    HatAlphaRelation am1 ae1 -> HatAlphaRelation am2 ae2 -> HatAlphaRelation (partialMC am1 am2) (partialEC ae1 ae2)) ->
  HatAlphaCompRelation cm ce -> PiCompRelation cm c prod partialMC -> alpha prod = proper ->
  SigmaCompRelation ce c proper partialEC.
Proof.
  intros. unfold SigmaCompRelation. unfold PiCompRelation in H3. 
  apply (aux_commutative_feature_product_product _ cm _ _ prod _ _ partialMC (E cm (top cm)));try(auto).
  - inversion H2. rewrite <- H7. rewrite <- H5. auto.
  - inversion H2. rewrite <- H5. apply H6.
Qed.
  


