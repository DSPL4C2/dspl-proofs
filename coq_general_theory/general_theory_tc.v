Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.Init.Wf.

Load add.
Load compositionalThing.

Class Property (Proper : Type) : Type :=
{
  emptyProperty : Proper
}.

Class Product (Prod : Type) {Proper : Type} `{Property Proper} : Type :=
{
  emptyProduct : Prod;
  alpha : Prod -> Proper
}.

Axiom AlphaEmpty : forall (Prod Proper : Type) `{Property Proper} `{Product Prod}, 
  alpha emptyProduct = emptyProperty.

Class PresenceCondition (PC : Type) : Type :=
{
  pcToADD : PC -> (ADD bool);
  confToVariable : (PC -> bool) -> variables
}.

Variable Prod Proper PC : Type.

Definition conf : Type := PC -> bool.

Axiom PCEquivalence : forall `{PresenceCondition PC} (pc : PC) (c : conf),
  pcToADD(pc)(confToVariable c) = c pc.

Inductive VariableStructure {X : Type} `{PresenceCondition PC}: Type :=
  | Base (x : X)
  | Choice (pc : PC) (s1 s2 : VariableStructure).

Definition AnnotativeModel `{Product Prod} {H : PresenceCondition PC} : Type := 
  @VariableStructure Prod H.

Definition AnnotativeExpression `{Property Proper} {H : PresenceCondition PC} : Type := 
  @VariableStructure Proper H.

Inductive PiRelation `{Product Prod} `{PresenceCondition PC} : AnnotativeModel -> 
  conf -> Prod -> Prop :=
  | BaseCasePi (p : Prod) (c:  conf) : PiRelation (Base p) c p
  | Choice1Pi (am1 am2 : AnnotativeModel) (p : Prod) (pc : PC) (c : conf) 
      (H1 : c pc = true) (H2 : PiRelation am1 c p) : PiRelation (Choice pc am1 am2) c p
  | Choice2Pi (am1 am2 : AnnotativeModel) (p : Prod) (pc : PC) (c : conf) 
      (H1 : c pc = false) (H2 : PiRelation am2 c p) : PiRelation (Choice pc am1 am2) c p.

Inductive SigmaRelation `{Property Proper} `{PresenceCondition PC} : AnnotativeExpression -> 
  conf -> Proper -> Prop :=
  | BaseCaseSig (p : Proper) (c:  conf) : SigmaRelation (Base p) c p
  | Choice1Sig (ae1 ae2 : AnnotativeExpression) (p : Proper) (pc : PC) (c : conf) 
      (H1 : c pc = true) (H2 : SigmaRelation ae1 c p) : SigmaRelation (Choice pc ae1 ae2) c p
  | Choice2Sig (ae1 ae2 : AnnotativeExpression) (p : Proper) (pc : PC) (c : conf) 
      (H1 : c pc = false) (H2 : SigmaRelation ae2 c p) : SigmaRelation (Choice pc ae1 ae2) c p.

Inductive HatAlphaRelation {Hp : Property Proper} `{@Product Prod Proper Hp} `{PresenceCondition PC} : 
  AnnotativeModel -> AnnotativeExpression -> Prop :=
  | BaseCase (prod : Prod) (proper : Proper) (H : alpha prod = proper) : 
      HatAlphaRelation (Base prod) (Base proper)
  | ChoiceCase (am1 am2 : AnnotativeModel) (ae1 ae2 : AnnotativeExpression) (pc : PC) 
      (H1: HatAlphaRelation am1 ae1) (H2: HatAlphaRelation am2 ae2) : 
      HatAlphaRelation (Choice pc am1 am2) (Choice pc ae1 ae2).

Theorem commutative_product_family_product `{Hp : Property Proper} `{@Product Prod Proper Hp} 
  `{PresenceCondition PC} : forall (am : AnnotativeModel) 
  (ae : AnnotativeExpression)(c : conf) (prod : Prod) (proper : Proper), 
  HatAlphaRelation am ae -> PiRelation am c prod -> alpha prod = proper -> SigmaRelation ae c proper.
Proof.
  intros. induction H1.
  - inversion H2. subst. constructor.
  - inversion H2. 
    + subst. apply Choice1Sig. auto. apply IHHatAlphaRelation1. apply H9.
    + subst. apply Choice2Sig. auto. apply IHHatAlphaRelation2. apply H9.
Qed.

Definition CompositionalModel `{Product Prod} `{PresenceCondition PC} : Type := 
  @CompositionalThing PC (AnnotativeModel).

Definition CompositionalExpression `{Property Proper} `{PresenceCondition PC}: Type :=
  @CompositionalThing PC (AnnotativeExpression).

Definition partialMCT `{Product Prod} `{PresenceCondition PC} : Type := AnnotativeModel -> AnnotativeModel -> AnnotativeModel. (* Partial Model Composition Type*)
Definition partialECT `{Property Proper} `{PresenceCondition PC} : Type := AnnotativeExpression -> AnnotativeExpression -> AnnotativeExpression. (* Partial Expression Composition Type*)
Definition partialADDCT `{Property Proper} `{PresenceCondition PC} : Type := (ADD Proper) -> (ADD Proper) -> (ADD Proper). (*Partial ADD Composition Type*)


Inductive HatAlphaCompRelation {Hp : Property Proper} `{@Product Prod Proper Hp} `{PresenceCondition PC} :
  CompositionalModel -> CompositionalExpression -> Prop :=
  | FMapHa (cm : CompositionalModel) (ce : CompositionalExpression) (H1 : cm.(top) = ce.(top))
    (H2 : forall (n : nat), HatAlphaRelation (cm.(E) n) (ce.(E) n)) (H3 : cm.(dependents) = ce.(dependents)) :
    HatAlphaCompRelation cm ce.

Inductive PiCompRelation_aux `{Product Prod} `{PresenceCondition PC} 
  : CompositionalModel -> AnnotativeModel -> list (PC * nat) -> conf -> partialMCT -> Prod -> Prop :=
  | NilListPi (cm : CompositionalModel) (am : AnnotativeModel) (c : conf) (prod : Prod)
      (partialMC : partialMCT) (H1 : PiRelation am c prod) : 
      PiCompRelation_aux cm am nil c partialMC prod
  | TruePCCasePi (cm : CompositionalModel) (am : AnnotativeModel) (t : list (PC * nat)) (c : conf) (prod1 prod2 : Prod)
      (h : (PC * nat)) (partialMC : partialMCT) (H1 : c (fst h) = true)
      (H2 : PiCompRelation_aux cm (cm.(E) (snd h)) (cm.(dependents) (snd h)) c partialMC prod2)
      (H3 : PiCompRelation_aux cm (partialMC am (Base prod2)) t c partialMC prod1) :
      PiCompRelation_aux cm am (h :: t) c partialMC prod1
  | FalsePCCasePi (cm : CompositionalModel) (am : AnnotativeModel) (t : list (PC * nat)) (c : conf) (prod : Prod)
      (h : (PC * nat)) (partialMC : partialMCT) (H1 : c (fst h) = false)
      (H2 : PiCompRelation_aux cm (partialMC am (Base emptyProduct)) t c partialMC prod) : 
       PiCompRelation_aux cm am (h :: t) c partialMC prod.
      
Inductive SigmaCompRelation_aux `{Property Proper} `{PresenceCondition PC} : 
  CompositionalExpression -> AnnotativeExpression -> list (PC * nat) -> conf -> partialECT -> Proper -> Prop :=
  | NilListSig (ce : CompositionalExpression) (ae : AnnotativeExpression) (c : conf) (proper : Proper)
      (partialEC : partialECT) (H1 : SigmaRelation ae c proper) : 
      SigmaCompRelation_aux ce ae nil c partialEC proper
  | TruePCCaseSig (ce : CompositionalExpression) (ae : AnnotativeExpression) (t : list (PC * nat)) (c : conf) (proper1 proper2 : Proper)
      (h : (PC * nat)) (partialEC : partialECT) (H1 : c (fst h) = true)
      (H2 : SigmaCompRelation_aux ce (ce.(E) (snd h)) (ce.(dependents) (snd h)) c partialEC proper2)
      (H3 : SigmaCompRelation_aux ce (partialEC ae (Base proper2)) t c partialEC proper1) :
      SigmaCompRelation_aux ce ae (h :: t) c partialEC proper1
  | FalsePCCaseSig (ce : CompositionalExpression) (ae : AnnotativeExpression) (t : list (PC * nat)) (c : conf) (proper : Proper)
      (h : (PC * nat)) (partialEC : partialECT) (H1 : c (fst h) = false)
      (H2 : SigmaCompRelation_aux ce (partialEC ae (Base emptyProperty)) t c partialEC proper) : 
       SigmaCompRelation_aux ce ae (h :: t) c partialEC proper.

Definition PiCompRelation `{Product Prod} `{PresenceCondition PC} 
  (cm : CompositionalModel) (c : conf) (p : Prod) (partialMC : partialMCT) : Prop :=
  PiCompRelation_aux cm (cm.(E) cm.(top)) (cm.(dependents) cm.(top)) c partialMC p.

Definition SigmaCompRelation `{Property Proper} `{PresenceCondition PC} (ce : CompositionalExpression) (c : conf) (p: Proper) (partialEC : partialECT) : Prop :=
  SigmaCompRelation_aux ce (ce.(E) ce.(top)) (ce.(dependents) ce.(top)) c partialEC p.

Theorem aux_commutative_feature_product_product {Hp : Property Proper}
  `{@Product Prod Proper Hp} `{PresenceCondition PC} : forall (l : list (PC * nat)) (cm : CompositionalModel) 
  (ce : CompositionalExpression) (c : conf) (prod : Prod) (proper : Proper) (ae : AnnotativeExpression)
  (partialMC : partialMCT) (am : AnnotativeModel) (partialEC : partialECT),
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

Theorem commutative_feature_product_product {Hp : Property Proper}
  `{@Product Prod Proper Hp} `{PresenceCondition PC} : forall (cm : CompositionalModel) 
  (ce : CompositionalExpression) (c : conf) (prod : Prod) (proper : Proper)
  (partialMC : partialMCT) (partialEC : partialECT),
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

Fixpoint HatSigma `{Property Proper} `{PresenceCondition PC} (ae : AnnotativeExpression) : ADD Proper :=
  match ae with
  | Base proper => constant proper
  | Choice pc ae1 ae2 => ite (pcToADD pc) (HatSigma ae1) (HatSigma ae2)
  end.

Theorem commutative_family_product_family `{Property Proper} `{PresenceCondition PC} :
  forall (ae : AnnotativeExpression) (c : conf), SigmaRelation ae c ((HatSigma ae) (confToVariable c)).
Proof.
  intros ae. induction ae.
  - intros. unfold HatSigma. unfold constant. constructor.
  - intros. destruct (c pc) eqn:E.
    + constructor. auto. unfold HatSigma. unfold ite. 
      rewrite PCEquivalence. rewrite E. auto.
    + apply Choice2Sig. auto. unfold HatSigma. unfold ite. 
      rewrite PCEquivalence. rewrite E. auto.
Qed.

Fixpoint zip {X Y : Type} (lx : list X) (ly : list Y) : list (X * Y) :=
  match lx, ly with
  | h1 :: t1, h2 :: t2 => (h1,h2) :: (zip t1 t2)
  | _, _ => nil
  end.

Inductive HatSigmaCompRelation `{Property Proper} `{PresenceCondition PC} : CompositionalExpression -> 
  nat -> partialADDCT -> (ADD Proper) -> Prop :=
  | NotDependents (ce : CompositionalExpression) (n : nat) (partialADDC : partialADDCT)
      (H1 : ce.(dependents) n = nil) : HatSigmaCompRelation ce n partialADDC (HatSigma (ce.(E) n))
  | HaveDependents (ce : CompositionalExpression) (n : nat) (partialADDC : partialADDCT) 
      (ladd : list (ADD Proper)) (lzip : list ((ADD Proper) * (PC * nat))) (H1 : ce.(dependents) n <> nil) 
      (H2 : lzip = zip ladd (ce.(dependents) n)) (H3 : length ladd = length (ce.(dependents) n))
      (H4 : forall x : (ADD Proper) * (PC * nat), In x lzip -> HatSigmaCompRelation ce (snd(snd x)) partialADDC (fst x)) :
      HatSigmaCompRelation ce n partialADDC (fold_left partialADDC ladd (HatSigma (ce.(E) n))).

Theorem zipnilr {X Y : Type} : forall (l : list X), zip l (@ nil Y) = nil.
Proof.
  intros. destruct l;simpl;unfold zip; reflexivity.
Qed.

Theorem zipLength {X Y : Type} : forall (l1 : list X) (l2 : list Y) (l3 : list (X * Y)),
  l3 = zip l1 l2 -> length l1 = length l2 -> length l1 = length l3.
Proof.
  induction l1;intros.
  - rewrite H. reflexivity.
  - destruct l2. discriminate H0. destruct l3. discriminate H.
    inversion H. simpl. rewrite <- H3. apply IHl1 in H3.
    rewrite H3. reflexivity. inversion H0. reflexivity.
Qed.

Theorem SigmaProperEquivalence: forall `{Property Proper} `{PresenceCondition PC},
  forall (ae : AnnotativeExpression) (c : conf) (p1 p2 : Proper),
  (SigmaRelation ae c p1 /\ SigmaRelation ae c p2) -> p1 = p2.
Proof.
  intros. destruct H1. induction ae.
  - inversion H1. inversion H2. rewrite H5 in H8. auto.
  - inversion H1;inversion H2.
    + apply IHae1. auto. auto.
    + rewrite H8 in H15. discriminate H15.
    + rewrite H8 in H15. discriminate H15.
    + apply IHae2. auto. auto.
Qed.
(* Acredito que seja possível provar, mas até o momento não consegui*)
Axiom SigmaCompProperEquivalence: forall `{Property Proper} `{PresenceCondition PC},
  forall (l : list (PC * nat)) (ce : CompositionalExpression) (ae : AnnotativeExpression) 
  (c : PC -> bool) (partialEC : partialECT) (p1 p2 : Proper),
  (SigmaCompRelation_aux ce ae l c partialEC p1 /\
  SigmaCompRelation_aux ce ae l c partialEC p2) -> p1 = p2.

Theorem mapComposition : forall (X Y Z : Type) (l : list X) (f : Y -> Z) (g : X -> Y),
  map f (map g l) = map (compose f g) l.
Proof.
  induction l.
  - intros. reflexivity.
  - intros. simpl. rewrite IHl. reflexivity.
Qed.

Theorem mapEquivalence : forall (X Y Z : Type) (l1 : list X) (l2 : list Y) (l3 : list (X * Y))
  (f1 : X -> Z) (f2 : X * Y -> Z), l3 = zip l1 l2 -> length l3 = length l1 -> 
  (forall x : X * Y, In x l3 -> f1 (fst x) = f2 x) -> map f1 l1 = map f2 l3.
Proof.
  intros X Y Z. induction l1;intros.
  - rewrite H. reflexivity.
  - destruct l2. rewrite zipnilr in H. rewrite H in H0. discriminate H0.
    destruct l3. discriminate H0. simpl. simpl in H. inversion H.
    inversion H0. rewrite <- H4. apply (IHl1 _ _ f1 f2) in H4.
    + rewrite H4. assert (H': f1 (fst p) = f2 p). apply H1.
      left. reflexivity. rewrite H3 in H'. simpl in H'. rewrite H'.
      reflexivity.
    + auto.
    + intros. apply H1. right. auto.
Qed.

Theorem foldlce `{Property Proper} `{PresenceCondition PC}:
  forall (ce : CompositionalExpression) (n : nat) (c : conf) (partialEC : partialECT)
    (partialADDC : partialADDCT) (ladd : list (ADD Proper)) (ae : AnnotativeExpression)
    (lzip : list ((ADD Proper) * (PC * nat))) (add : ADD Proper) , lzip = zip ladd (dependents ce n) ->
    length ladd = length (dependents ce n) -> (forall x : ADD Proper * (PC * nat), In x lzip ->
    HatSigmaCompRelation ce (snd (snd x)) partialADDC (fst x)) -> 
    (forall x : ADD Proper * (PC * nat), In x lzip ->
    SigmaCompRelation_aux ce (E ce (snd (snd x))) (dependents ce (snd (snd x))) c partialEC
    (fst x (confToVariable c))) ->
    (SigmaCompRelation_aux ce ae (dependents ce n) c
    partialEC ((fold_left partialADDC ladd add)
    (confToVariable c)) <-> SigmaCompRelation_aux ce 
    (fold_left partialEC (map (fun (x : (ADD Proper) * (PC * nat)) => 
    if (c (fst (snd x))) then (Base ((fst x) (confToVariable c))) else (Base emptyProperty))
    lzip) ae) nil c partialEC (fold_left partialADDC ladd add
    (confToVariable c))).
Proof.
  intros ce n. induction (dependents ce n).
  - intros. split.
    + intros. rewrite zipnilr in H1. rewrite H1. simpl. auto.
    + intros. rewrite zipnilr in H1. rewrite H1 in H5. simpl in H5. auto.
  - intros. destruct ladd. discriminate H2. split.
    + intros. simpl. simpl in H5. inversion H5.
      * simpl in H1. rewrite H1. simpl. rewrite H8.
        assert (H' : In (a0,a) lzip). rewrite H1. simpl.
        left. reflexivity. apply H4 in H'. simpl in H'.
        assert (H'' : proper2 = a0 (confToVariable c)).
        apply (SigmaCompProperEquivalence (dependents ce (snd a)) ce
        (E ce (snd a)) c partialEC). split;auto. rewrite <- H''.
        destruct lzip. discriminate H1. inversion H1. rewrite <- H18.
        apply (IHl c partialEC partialADDC _
        (partialEC ae (Base proper2)) _
        (partialADDC add a0)) in H18.
        { destruct H18. apply H16. auto. }
        { simpl in H2. inversion H2. reflexivity. }
        { intros. apply H3. simpl. right. auto. }
        { intros. apply H4. simpl. right. auto. }
      * simpl in H1. rewrite H1. simpl. rewrite H10. destruct lzip.
        discriminate H1. inversion H1. rewrite <- H17.
        apply (IHl c partialEC partialADDC _ 
        (partialEC ae (Base emptyProperty)) _
        (partialADDC add a0))in H17.
        { apply H17. auto. }
        { inversion H2. reflexivity. }
        { intros. apply H3. right. auto. }
        { intros. apply H4. right. auto. }
    + intros. destruct lzip. discriminate H1. inversion H1.
      rewrite H7 in H5. simpl. simpl in H5. destruct (c (fst a)) eqn:E.
      * apply (TruePCCaseSig _ _ _ _ _ (a0 (confToVariable c))).
        { auto. }
        { assert (H'': In p (p::lzip)). left. reflexivity.
          apply H4 in H''. rewrite H7 in H''. simpl in H''. auto. }
        { apply (IHl c partialEC partialADDC _ 
          (partialEC ae (Base (a0 (confToVariable c))))
          _ (partialADDC add a0)) in H8.
          { apply H8. auto. }
          { inversion H2. reflexivity. }
          { intros. apply H3. right. auto. }
          { intros. apply H4. right. auto. } }
      * apply FalsePCCaseSig. auto. apply 
        (IHl c partialEC partialADDC _ 
        (partialEC ae (Base emptyProperty))
        _ (partialADDC add a0)) in H8.
        { apply H8. auto. }
        { inversion H2. reflexivity. }
        { intros. apply H3. right. auto. }
        { intros. apply H4. right. auto. }
Qed.

Theorem commutative_feature_family_feature_produc `{Property Proper} `{PresenceCondition PC} :
  forall (ce : CompositionalExpression) (c : conf) (partialEC : partialECT) 
    (partialADDC : partialADDCT) (add : ADD Proper), 
    (forall (ae : AnnotativeExpression) (l : list AnnotativeExpression),
    fold_left partialADDC (map HatSigma l) (HatSigma ae) = 
    HatSigma(fold_left partialEC l ae)) -> (forall (x : ADD Proper * (PC * nat))
    (listzip : list ((ADD Proper) * (PC * nat))) (ce : CompositionalExpression),
    In x listzip -> c (fst (snd x)) = false -> HatSigmaCompRelation ce (snd (snd x)) 
    partialADDC (fst x) -> (fst x) (confToVariable c) = emptyProperty) -> 
    (forall (v : variables) (a1 a2 : ADD Proper) (l1 l2 : list (ADD Proper)),
    (a1 v = a2 v /\ map (fun a : (ADD Proper) => a v) l1 = map 
    (fun a : (ADD Proper) => a v) l2 )-> (fold_left partialADDC l1 a1) v = 
    (fold_left partialADDC l2 a2) v) ->
    HatSigmaCompRelation ce ce.(top) partialADDC add -> 
    SigmaCompRelation ce c (add (confToVariable c)) partialEC.
Proof.
  intros. unfold SigmaCompRelation. induction H4.
  - rewrite H4. constructor. induction (E ce n). 
    + constructor.
    + unfold HatSigma. unfold ite. destruct (c pc) eqn:E';
      constructor;auto;rewrite PCEquivalence;rewrite E';auto.
  - assert (H': (SigmaCompRelation_aux ce (E ce n) (dependents ce n) c
    partialEC ((fold_left partialADDC ladd (HatSigma (E ce n)))
    (confToVariable c)) <-> SigmaCompRelation_aux ce 
    (fold_left partialEC (map (fun (x : (ADD Proper) * (PC * nat)) => 
    if (c (fst (snd x))) then (Base ((fst x) (confToVariable c))) 
    else (Base emptyProperty)) lzip) (E ce n)) nil c partialEC 
    (fold_left partialADDC ladd (HatSigma (E ce n)) (confToVariable c)))).
    apply foldlce;auto. apply H'. constructor. assert (H'': SigmaRelation
    (fold_left partialEC (map (fun x : ADD Proper * (PC * nat) =>
    if c (fst (snd x)) then Base (fst x (confToVariable c))
    else Base emptyProperty) lzip) (E ce n)) c ((HatSigma
    (fold_left partialEC (map (fun x : ADD Proper * (PC * nat) =>
    if c (fst (snd x)) then Base (fst x (confToVariable c))
    else Base emptyProperty) lzip) (E ce n))) (confToVariable c))).
    apply commutative_family_product_family. assert (H''' : (fold_left 
    partialADDC ladd (HatSigma (E ce n))) (confToVariable c) =  HatSigma 
    (fold_left partialEC
    (map (fun x : ADD Proper * (PC * nat) => if c (fst (snd x)) then Base
     (fst x (confToVariable c)) else Base emptyProperty) lzip) 
    (E ce n)) (confToVariable c)).
    + rewrite <- H1. rewrite mapComposition. unfold compose. apply H3.
      split. reflexivity. rewrite mapComposition. unfold compose.
      apply (mapEquivalence _ _ _ _ (dependents ce n)).
      * auto.
      * symmetry. apply (zipLength _ (dependents ce n));auto.
      * intros. destruct (c (fst (snd x))) eqn: E.
        { simpl. unfold constant. reflexivity. }
        { simpl. unfold constant. apply (H2 _ lzip ce);try(auto). }
    + rewrite H'''. auto.
Qed.

Theorem commutative_feature_family_product {Hp : Property Proper}
  `{@Product Prod Proper Hp} `{PresenceCondition PC} : forall (cm : CompositionalModel) 
  (ce : CompositionalExpression) (c : conf) (prod : Prod) (proper : Proper)
  (add : ADD Proper) (partialMC : partialMCT) (partialEC : partialECT) 
  (partialADDC : partialADDCT), ( forall (am1 am2 : AnnotativeModel) 
  (ae1 ae2 : AnnotativeExpression), HatAlphaRelation am1 ae1 -> HatAlphaRelation am2 ae2 
  -> HatAlphaRelation (partialMC am1 am2) (partialEC ae1 ae2)) -> (forall 
  (x : ADD Proper * (PC * nat)) (listzip : list ((ADD Proper) * (PC * nat))) 
  (ce : CompositionalExpression), In x listzip -> c (fst (snd x)) = false -> 
  HatSigmaCompRelation ce (snd (snd x)) partialADDC (fst x) -> (fst x) 
  (confToVariable c) = emptyProperty) -> (forall (ae : AnnotativeExpression) 
  (l : list AnnotativeExpression), fold_left partialADDC (map HatSigma l) (HatSigma ae) = 
  HatSigma(fold_left partialEC l ae)) -> (forall (v : variables) (a1 a2 : ADD Proper) 
  (l1 l2 : list (ADD Proper)), (a1 v = a2 v /\ map (fun a : (ADD Proper) => a v) l1 = map 
  (fun a : (ADD Proper) => a v) l2 )-> (fold_left partialADDC l1 a1) v = 
  (fold_left partialADDC l2 a2) v)  -> PiCompRelation cm c prod partialMC -> 
  alpha prod = proper -> HatAlphaCompRelation cm ce -> 
  HatSigmaCompRelation ce (top ce) partialADDC add -> add (confToVariable c) = proper.
Proof.
  intros. apply (commutative_feature_product_product cm ce c prod proper) in H1;try(auto).
  apply (commutative_feature_family_feature_produc ce c _ _ add) in  H3;try(auto). 
  unfold SigmaCompRelation in *. apply (SigmaCompProperEquivalence (dependents ce (top ce))
  ce (E ce (top ce)) c partialEC). split;auto.
Qed.






