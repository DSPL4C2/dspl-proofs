Inductive Product {X : Type} : Type :=
  | Prod (x: X).

Inductive Property {X : Type} : Type :=
  | Proper (x: X).

Inductive AlphaRelation {X Y : Type} : @Product X -> @Property Y -> (Product -> Property ) -> Prop :=
  | AR prod proper alpha (H : alpha prod = proper) : AlphaRelation prod proper alpha.

Inductive PresenceCondition {X : Type} : Type :=
  | PC (x : X).

Inductive ConfSatisfyPC {X : Type} : @PresenceCondition X -> (PresenceCondition -> bool) -> Prop :=
  | Satisfy pc conf (H: conf pc = true) : ConfSatisfyPC pc conf.

Inductive VariableStructure (X Y : Type) : Type :=
  | Base (x : X)
  | Choice (pc : @PresenceCondition Y) (s1 s2 : VariableStructure X Y).

Definition AnnotativeModel {X Y : Type} : Type := VariableStructure (@Product X) Y.

Definition AnnotativeExpression {X Y : Type} : Type := VariableStructure (@Property X) Y.

Inductive PiRelation {X Y : Type} : AnnotativeModel -> (PresenceCondition -> bool) -> Product -> Prop :=
  | BaseCasePi (p : @Product X) (c: @PresenceCondition Y -> bool) : PiRelation (Base (Product) Y p) c p
  | Choice1Pi (am1 am2 : AnnotativeModel) (p : @Product X) (pc : @PresenceCondition Y) (c : PresenceCondition -> bool) 
      (H1 : c pc = true) (H2 : PiRelation am1 c p) : PiRelation (Choice (Product) Y pc am1 am2) c p
  | Choice2Pi (am1 am2 : AnnotativeModel) (p : @Product X) (pc : @PresenceCondition Y) (c : PresenceCondition -> bool) 
      (H1 : c pc = false) (H2 : PiRelation am2 c p) : PiRelation (Choice (Product) Y pc am1 am2) c p.

Inductive SigmaRelation {X Y : Type} : AnnotativeExpression -> (PresenceCondition -> bool) -> Property -> Prop :=
  | BaseCaseSig (p : @Property X) (c: @PresenceCondition Y -> bool) : SigmaRelation (Base (Property) Y p) c p
  | Choice1Sig (ae1 ae2 : AnnotativeExpression) (p : @Property X) (pc : @PresenceCondition Y) (c : PresenceCondition -> bool) 
      (H1 : c pc = true) (H2 : SigmaRelation ae1 c p) : SigmaRelation (Choice (Property) Y pc ae1 ae2) c p
  | Choice2Sig (ae1 ae2 : AnnotativeExpression) (p : @Property X) (pc : @PresenceCondition Y) (c : PresenceCondition -> bool) 
      (H1 : c pc = false) (H2 : SigmaRelation ae2 c p) : SigmaRelation (Choice (Property) Y pc ae1 ae2) c p.

Inductive HatAlphaRelation {X Y Z: Type} : AnnotativeModel -> AnnotativeExpression -> (Product -> Property) -> Prop :=
  | BaseCase (prod : @Product X) (proper : @Property Y) (alpha : Product -> Property) 
      (H : AlphaRelation prod proper alpha) : HatAlphaRelation (Base (Product) Z prod) (Base (Property) Z proper) alpha
  | ChoiceCase (am1 am2 : AnnotativeModel) (ae1 ae2 : AnnotativeExpression) (alpha : Product -> Property) 
      (pc : @PresenceCondition Z) (H1: HatAlphaRelation am1 ae1 alpha) (H2: HatAlphaRelation am2 ae2 alpha) : 
      HatAlphaRelation (Choice (Product) Z pc am1 am2) (Choice (Property) Z pc ae1 ae2) alpha.
