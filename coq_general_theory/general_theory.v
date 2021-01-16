Inductive Product : Type.

Inductive Property : Type.

Inductive AlphaRelation : Product -> Property -> (Product -> Property ) -> Prop :=
  | AR prod proper alpha (H : alpha prod = proper) : AlphaRelation prod proper alpha.

Inductive PresenceCondition : Type.

Inductive ConfSatisfyPC : PresenceCondition -> (PresenceCondition -> bool) -> Prop :=
  | Satisfy pc conf (H: conf pc = true) : ConfSatisfyPC pc conf.

Inductive VariableStructure (X : Type) : Type :=
  | Base (x : X)
  | Choice (pc : PresenceCondition) (s1 s2 : VariableStructure X).

Definition AnnotativeModel : Type := VariableStructure Product.

Definition AnnotativeExpression : Type := VariableStructure Property.

Inductive PiRelation : AnnotativeModel -> (PresenceCondition -> bool) -> Product -> Prop :=
  | BaseCasePi (p : Product) (c: PresenceCondition -> bool) : PiRelation (Base (Product) p) c p
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
      (H : AlphaRelation prod proper alpha) : HatAlphaRelation (Base (Product) prod) (Base (Property) proper) alpha
  | ChoiceCase (am1 am2 : AnnotativeModel) (ae1 ae2 : AnnotativeExpression) (alpha : Product -> Property) 
      (pc : PresenceCondition) (H1: HatAlphaRelation am1 ae1 alpha) (H2: HatAlphaRelation am2 ae2 alpha) : 
      HatAlphaRelation (Choice (Product) pc am1 am2) (Choice (Property) pc ae1 ae2) alpha.
