Inductive Product : Type.

Inductive Property : Type.

Inductive PresenceCondition : Type.

Inductive ConfSatisfyPC : PresenceCondition -> (PresenceCondition -> bool) -> Prop :=
  | Satisfy pc conf (H: conf pc = true) : ConfSatisfyPC pc conf.

Inductive VariableStructure (X : Type) : Type :=
  | Base (x : X)
  | Choice (pc : PresenceCondition) (s1 s2 : VariableStructure X).

Axiom variable_Structure_Injection_Base : 
  forall (X : Type) (x1 x2 : X), Base X x1 = Base X x2 -> x1 = x2.
Axiom variable_Structure_Injection_Choice : 
  forall (X : Type) (pc1 pc2 : PresenceCondition) (s1 s2 s3 s4 : VariableStructure X),
    Choice X pc1 s1 s2 = Choice X pc2 s3 s4 -> pc1 = pc2 /\ s1 = s3 /\ s2 = s4.

Definition AnnotativeModel : Type := VariableStructure Product.

Definition AnnotativeExpression : Type := VariableStructure Property.

Inductive PiRelation : AnnotativeModel -> (PresenceCondition -> bool) -> Product -> Prop :=
  | BaseCasePi (p: Product) (c: PresenceCondition -> bool) : PiRelation (Base Product p) c p
  | Choice1Pi (am1 am2 : AnnotativeModel) (p : Product) (pc : PresenceCondition) (c : PresenceCondition -> bool) 
      (H1 : c pc = true) (H2 : PiRelation am1 c p) : PiRelation (Choice (Product) pc am1 am2) c p
  | Choice2Pi (am1 am2 : AnnotativeModel) (p : Product) (pc : PresenceCondition ) (c : PresenceCondition -> bool) 
      (H1 : c pc = false) (H2 : PiRelation am2 c p) : PiRelation (Choice (Product) pc am1 am2) c p.

Inductive SigmaRelation : AnnotativeExpression -> (PresenceCondition -> bool) -> Property -> Prop :=
  | BaseCaseSig (p : Property) (c: PresenceCondition -> bool) : SigmaRelation (Base (Property) p) c p
  | Choice1Sig (ae1 ae2 : AnnotativeExpression) (p : Property) (pc : PresenceCondition) (c : PresenceCondition -> bool) 
      (H1 : c pc = true) (H2 : SigmaRelation ae1 c p) : SigmaRelation (Choice (Property) pc ae1 ae2) c p
  | Choice2Sig (ae1 ae2 : AnnotativeExpression) (p : Property) (pc : PresenceCondition) (c : PresenceCondition -> bool) 
      (H1 : c pc = false) (H2 : SigmaRelation ae2 c p) : SigmaRelation (Choice (Property) pc ae1 ae2) c p.

Inductive HatAlphaRelation : AnnotativeModel -> AnnotativeExpression -> (Product -> Property) -> Prop :=
  | BaseCase (prod : Product) (proper : Property) (alpha : Product -> Property) 
      (H : alpha prod = proper) : HatAlphaRelation (Base (Product) prod) (Base (Property) proper) alpha
  | ChoiceCase (am1 am2 : AnnotativeModel) (ae1 ae2 : AnnotativeExpression) (alpha : Product -> Property) 
      (pc : PresenceCondition) (H1: HatAlphaRelation am1 ae1 alpha) (H2: HatAlphaRelation am2 ae2 alpha) : 
      HatAlphaRelation (Choice (Product) pc am1 am2) (Choice (Property) pc ae1 ae2) alpha.

Theorem commutative_product_family_product : 
  forall (am : AnnotativeModel) (ae : AnnotativeExpression) (c : PresenceCondition -> bool) 
         (alpha : Product -> Property) (prod : Product) (proper : Property),
    HatAlphaRelation am ae alpha -> PiRelation am c prod -> alpha prod = proper -> SigmaRelation ae c proper.
Proof.
  intros. induction H.
  - simple inversion H0.
    + apply variable_Structure_Injection_Base in H2. rewrite H2 in H4.
      rewrite H4 in H. rewrite H in H1. rewrite H1. constructor.
    + discriminate H4.
    + discriminate H4.
  - simple inversion  H0.
    + discriminate H3.
    + intros. apply variable_Structure_Injection_Choice in H5.
      destruct H5. destruct H8. subst. apply Choice1Sig.
      * apply H3.
      * apply IHHatAlphaRelation1. apply H4. reflexivity.
    + intros. apply variable_Structure_Injection_Choice in H5.
      destruct H5. destruct H8. subst. apply Choice2Sig.
      * apply H3.
      * apply IHHatAlphaRelation2. apply H4. reflexivity.
Qed.
