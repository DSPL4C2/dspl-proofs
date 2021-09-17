Require Import FSets.

Load zip.
Load aux_theorems.
Load model_evolution.

Fixpoint featureFamily'Aux {Asset model analysis :Type}
  {H1 : @Analysis analysis Asset} {H2 : @Model model Asset}
  (rdg : RDG) (delta : RDG -> Evolution) : (string * (ADD float)) := 
  match rdg with
  | RDG_leaf s a => featureFamily (evolutionRDG rdg delta)
  | RDG_cons s a deps => match (delta rdg) with
                       | ID => featureFamily rdg
                       | Message => partialFeatureFamilyStep (evolutionRDG rdg delta)
                          (map (fun (x : RDG) => featureFamily'Aux (x) delta) deps)
                       | PC => partialFeatureFamilyStep (evolutionRDG rdg delta)
                          (map (fun (x : RDG) => featureFamily'Aux (x) delta) deps)
                       | SubsequentModelEvol => partialFeatureFamilyStep rdg
                          (map (fun (x : RDG) => featureFamily'Aux (x) delta) deps)
                       | AddFeature => partialFeatureFamilyStep (evolutionRDG rdg delta)
                          ((featureFamily (AddedRDG rdg delta))::(map
                          (fun (x : RDG) => featureFamily'Aux (x) delta) deps))
                       | RemoveFeature => partialFeatureFamilyStep (evolutionRDG rdg delta)
                          (ADDdepsRmvCase rdg delta 
                          (map (fun (x : RDG) => featureFamily'Aux (x) delta) deps))
                       end
  end.

Definition featureFamily' {Asset model analysis :Type} `{@Analysis analysis Asset}
  `{@Model model Asset}
  (mod : model) (delta : RDG -> Evolution) : (string * (ADD float)) := 
  featureFamily'Aux (buildRDG mod) delta.

Axiom well_founded_In_rdg : forall (Asset : Type),
  well_founded (fun r1 r2 : @RDG Asset => In r1 (deps r2)).

(*Theorem that describe the behaviour of the partialFeatureFamilyStep in relation to featureFamily.
  Used in cases which the evolution case is different then ID*)

Theorem partialFeatureFamilyStepEquivalence {Asset model analysis: Type}
  `{@Analysis analysis Asset} `{@Model model Asset} : forall (rdg : RDG),
  partialFeatureFamilyStep rdg (map featureFamily (deps rdg)) = featureFamily rdg.
Proof.
  intros. destruct rdg;
  simpl; unfold partialFeatureFamilyStep; reflexivity.
Qed.

Theorem well_founded_phi_equivalence {Asset model analysis : Type} 
  `{@Analysis analysis Asset} `{@Model model Asset} :
  forall delta : RDG -> Evolution, (forall rx : RDG, (forall ry : RDG,
  (fun r1 r2 : RDG => In r1 (deps r2)) ry rx -> 
  (fun r : RDG => featureFamily'Aux r delta = featureFamily (evolutionRDG r delta)) ry) ->
  (fun r : RDG => featureFamily'Aux r delta = featureFamily (evolutionRDG r delta)) rx) ->
  forall r : RDG, (fun r : RDG => featureFamily'Aux r delta = 
  featureFamily (evolutionRDG r delta)) r.
Proof.
  intros delta. apply well_founded_ind. apply well_founded_In_rdg.
Qed.

Theorem map_phi_evolution_theorem {Asset model analysis :Type} 
  `{@Analysis analysis Asset} `{@Model model Asset} : forall
  (delta : RDG -> Evolution) (l : list RDG), map featureFamily 
  (map (fun r : RDG => evolutionRDG r delta) l) =
  map (fun r : RDG => featureFamily (evolutionRDG r delta)) l.
Proof.
  intros. induction l.
  - reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

Ltac map_deps_evolution_commutativity rdg delta D H'':=
  assert (H'' : map (fun r : RDG => featureFamily (evolutionRDG r delta)) 
  (deps rdg) = map featureFamily 
  (deps (evolutionRDG rdg delta)));
  try(apply (commutativePhiEvolution);rewrite D;split;
  intros H''';discriminate H''').

Ltac map_pFeatureFamily_same_list H'' :=
  assert (H'' :
  forall (r : RDG) (l1 l2 : list (string * (ADD float))), l1 = l2 ->
  partialFeatureFamilyStep r l1 = partialFeatureFamilyStep r l2); 
  try(intros r l1 l2 Hl;rewrite Hl;reflexivity).

Ltac Phi'Equivalence_list_pFeatureFamily deps0 ass s delta H :=
  assert (H' : (map (fun x : RDG => featureFamily'Aux x delta) deps0) =
  (map featureFamily (deps (evolutionRDG (RDG_cons s ass deps0) delta))) ->
  partialFeatureFamilyStep (evolutionRDG (RDG_cons s ass deps0) delta)
  (map (fun x : RDG => featureFamily'Aux x delta) deps0) =
  partialFeatureFamilyStep (evolutionRDG (RDG_cons s ass deps0) delta)
  (map featureFamily (deps (evolutionRDG (RDG_cons s ass deps0) delta))));
  try(intros;rewrite H;reflexivity).

Ltac map_pFeatureFamily_evolution deps0 ass s delta:=
  assert (Hsub : partialFeatureFamilyStep (RDG_cons s ass deps0) 
  (map (fun x : RDG => featureFamily'Aux x delta) deps0) = partialFeatureFamilyStep 
  (evolutionRDG (RDG_cons s ass deps0) delta) 
  (map (fun x : RDG => featureFamily'Aux x delta) deps0));
  try(apply (subsequentModelAxiom );auto).

Ltac simplify_case_analysis deps0 ass s delta:=
  destruct (delta (RDG_cons s ass deps0)) eqn:D;
  simpl; rewrite D; try (apply partialFeatureFamilyStepIDEvolution in D; 
  rewrite D;reflexivity); rewrite <- (partialFeatureFamilyStepEquivalence
  (evolutionRDG (RDG_cons s ass deps0) delta)).

Ltac finish_not_add_remove_case ass deps0 s delta D H' H'':= 
    map_deps_evolution_commutativity (RDG_cons s ass deps0) delta D H'';
    rewrite <- H'' in H' at 1; auto.

Ltac list_axiom := assert (H''' : 
    forall (l1 l2 : list (string * (ADD float))) (r : (string * (ADD float))),
    l1 = l2 -> r::l1 = r::l2);try(intros l1 l2 r0 Hl12;rewrite Hl12; reflexivity).

Hint Resolve In_map_theorem : core.
Hint Resolve map_phi_evolution_theorem : core.

Theorem Phi'EquivalenceAux {Asset model analysis :Type}
  `{@Analysis analysis Asset} `{@Model model Asset} :
  forall (rdg : RDG) (delta : RDG -> Evolution),
  featureFamily'Aux rdg delta = featureFamily (evolutionRDG rdg delta).
Proof.
  intros. apply well_founded_phi_equivalence. intros.
  destruct rx. reflexivity.
  Phi'Equivalence_list_pFeatureFamily deps0 ass s delta H2.
  simplify_case_analysis deps0 ass s delta;
  try (finish_not_add_remove_case ass deps0 s delta D H' H'').
  (*Add Feature Case*)
  - map_pFeatureFamily_same_list H''.
    apply depsAddEvolution in D.
    destruct D as [r [lr [H3 [H4 H5]]]]. list_axiom. 
    apply H''. rewrite H3. simpl. 
    rewrite H4. apply H'''. rewrite H5. simpl.
    rewrite map_phi_evolution_theorem. auto.
  (*Subsequent Model Evolution Case*)
  - assert (Hsub : partialFeatureFamilyStep (RDG_cons s ass deps0) 
    (map (fun x : RDG => featureFamily'Aux x delta) deps0) = partialFeatureFamilyStep 
    (evolutionRDG (RDG_cons s ass deps0) delta)
    (map (fun x : RDG => featureFamily'Aux x delta) deps0)).
    apply subsequentModelAxiom in D.
    unfold partialFeatureFamilyStep. unfold featureOperation.
    destruct (evolutionRDG (RDG_cons s ass deps0) delta);
    destruct D; simpl in H2; simpl in H3; rewrite H2; rewrite H3; auto.
    rewrite Hsub. map_pFeatureFamily_same_list H'''. apply H'''.
    assert (H'''' : map (fun r : RDG => featureFamily (evolutionRDG r delta)) 
    (deps (RDG_cons s ass deps0)) =
    map featureFamily (deps (evolutionRDG (RDG_cons s ass deps0) delta))).
    try(apply (commutativePhiEvolution);rewrite D;split;
    intros H'''';discriminate H''''). rewrite <- H''''.
    apply In_map_theorem. simpl. apply H1.
  (*Remove Feature Case*)
  - apply In_map_theorem in H1. simpl in H1. rewrite H1.
    apply (RemoveFeatureAxiom model _ analysis) in D. rewrite <- D.
    reflexivity.
Qed.

Theorem Phi'Equivalence {Asset model analysis :Type} `{@Analysis analysis Asset}
  `{@Model model Asset} : forall (m : model) (delta : RDG -> Evolution), 
  featureFamily' m delta = featureFamily (evolutionRDG (buildRDG m) delta).
Proof.
  intros. unfold featureFamily'. apply Phi'EquivalenceAux.
Qed.