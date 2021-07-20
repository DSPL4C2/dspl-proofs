Require Import FSets.

Load zip.
Load aux_theorems.
Load model_evolution.

Fixpoint featureFamily'Aux {model asset :Type} {H1 : Asset asset} {H2 : Model model}
  (rdg : RDG) (delta : RDG -> Evolution) : (ADD float) := 
  match rdg with
  | RDG_leaf a => featureFamily (evolutionRDG rdg delta)
  | RDG_cons a deps => match (delta rdg) with
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
                       (*O coq estava reclamando da recursão ao 
                         aplicar uma função nos deps, então foi preciso
                         ajustar a função RemoveADDdeps para mudar a lista de ADDs,
                         e não a lista de RDG*)
                       | RemoveFeature => partialFeatureFamilyStep (evolutionRDG rdg delta)
                          (ADDdepsRmvCase rdg delta 
                          (map (fun (x : RDG) => featureFamily'Aux (x) delta) deps))
                       end
  end.

Definition featureFamily' {model asset :Type} `{Asset asset} `{Model model}
  (mod : model) (delta : RDG -> Evolution) : ADD float := 
  featureFamily'Aux (buildRDG mod) delta.

Axiom well_founded_In_rdg : forall (asset : Type) `{Asset asset},
  well_founded (fun r1 r2 : RDG => In r1 (deps r2)).

Axiom featureOperation_RDG_leaf : forall (asset model : Type) (Hass : Asset asset) 
  (Hmodel : @Model model asset Hass), forall (rdg : RDG) (ass : asset), 
  rdg = RDG_leaf ass -> familyOperation (featureOperation rdg) nil = 
  liftedExprEvaluation (featureOperation rdg).

(*Teorema que descreve o comportamento do partialFeatureFamilyStep em relação ao phi.
  Utilizado para os casos em que a evolução não é ID*)

Theorem partialFeatureFamilyStepEquivalence : forall (model asset: Type) `{Asset asset} `{Model model},
  forall (rdg : RDG),
  partialFeatureFamilyStep rdg (map featureFamily (deps rdg)) = featureFamily rdg.
Proof.
  intros. destruct rdg.
  - unfold featureFamily at 2. simpl. apply (featureOperation_RDG_leaf _ _ _ _ _ ass).
    reflexivity.
  - simpl. unfold partialFeatureFamilyStep. reflexivity.
Qed.

Theorem well_founded_phi_equivalence {model asset :Type} 
  `{Asset asset} `{Model model} : forall delta : RDG -> Evolution,
  (forall rx : RDG, (forall ry : RDG,
  (fun r1 r2 : RDG => In r1 (deps r2)) ry rx -> 
  (fun r : RDG => featureFamily'Aux r delta = featureFamily (evolutionRDG r delta)) ry) ->
  (fun r : RDG => featureFamily'Aux r delta = featureFamily (evolutionRDG r delta)) rx) ->
  forall r : RDG, (fun r : RDG => featureFamily'Aux r delta = 
  featureFamily (evolutionRDG r delta)) r.
Proof.
  intros delta. apply well_founded_ind. apply well_founded_In_rdg.
Qed.

Theorem map_phi_evolution_theorem {model asset :Type} 
  `{Asset asset} `{Model model} : forall (delta : RDG -> Evolution)
  (l : list RDG), map featureFamily (map (fun r : RDG => evolutionRDG r delta) l) = 
  map (fun r : RDG => featureFamily (evolutionRDG r delta)) l.
Proof. 
  intros. induction l.
  - reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

Theorem Phi'EquivalenceAux {model asset :Type} `{Asset asset} `{Model model} :
  forall (rdg : RDG) (delta : RDG -> Evolution),
  featureFamily'Aux rdg delta = featureFamily (evolutionRDG rdg delta).
Proof.
  intros. apply well_founded_phi_equivalence. intros.
  destruct rx. reflexivity.
  (*addicting a hypothesis that is used in many cases of the (delta rdg) case analisys*)
  assert (H' : (map (fun x : RDG => featureFamily'Aux x delta) deps0) =
  (map featureFamily (deps (evolutionRDG (RDG_cons ass deps0) delta))) ->
  partialFeatureFamilyStep (evolutionRDG (RDG_cons ass deps0) delta)
  (map (fun x : RDG => featureFamily'Aux x delta) deps0) =
  partialFeatureFamilyStep (evolutionRDG (RDG_cons ass deps0) delta)
  (map featureFamily (deps (evolutionRDG (RDG_cons ass deps0) delta)))).
  { intros. rewrite H3. reflexivity. }
  destruct (delta (RDG_cons ass deps0)) eqn:D;
  simpl; rewrite D; try (apply (partialFeatureFamilyStepIDEvolution model asset) in D; 
  rewrite D;reflexivity); rewrite <- (partialFeatureFamilyStepEquivalence _ asset
  (evolutionRDG (RDG_cons ass deps0) delta)).
  (*Message Case*)
  - apply H'.
    assert (H'' : map (fun r : RDG => featureFamily (evolutionRDG r delta)) 
    (deps (RDG_cons ass deps0)) = map featureFamily 
    (deps (evolutionRDG (RDG_cons ass deps0) delta))).
    { apply (commutativePhiEvolution _ asset). rewrite D. split;
    intros H''';discriminate H'''. }
    rewrite <- H''. simpl. simpl in H2. apply In_map_theorem.
    apply H2.
  (*Presence Condition Case*)
  - apply H'.
    assert (H'' : map (fun r : RDG => featureFamily (evolutionRDG r delta)) 
    (deps (RDG_cons ass deps0)) = map featureFamily
    (deps (evolutionRDG (RDG_cons ass deps0) delta))).
    { apply (commutativePhiEvolution _ asset). rewrite D. split;
    intros H''';discriminate H'''. }
    rewrite <- H''. simpl. simpl in H2. apply In_map_theorem.
    apply H2.
  (*Add Feature Case*)
  - assert (H'' :
    forall (r : RDG) (l1 l2 : list (ADD float)), l1 = l2 ->
    partialFeatureFamilyStep r l1 = partialFeatureFamilyStep r l2). intros. rewrite H3. reflexivity.
    apply H''. apply (depsAddEvolution model asset) in D.
    destruct D. destruct H3. destruct H3. destruct H4. rewrite H3. simpl.
    rewrite H4. assert (H''' : forall (l1 l2 : list (ADD float)) (r : ADD float),
    l1 = l2 -> r::l1 = r::l2). intros. rewrite H6. reflexivity.
    apply H'''. rewrite H5. simpl. rewrite map_phi_evolution_theorem.
    apply In_map_theorem. apply H2.
  (*Subsequent Model Evolution Case*)
  - assert (Hsub : partialFeatureFamilyStep (RDG_cons ass deps0) 
    (map (fun x : RDG => featureFamily'Aux x delta) deps0) = partialFeatureFamilyStep 
    (evolutionRDG (RDG_cons ass deps0) delta) 
    (map (fun x : RDG => featureFamily'Aux x delta) deps0)). 
    apply (subsequentModelAxiom _ asset). auto.
    rewrite Hsub. assert (H'' : (map (fun x : RDG => featureFamily'Aux x delta) deps0) =
    (map featureFamily (deps (evolutionRDG (RDG_cons ass deps0) delta))) ->
    partialFeatureFamilyStep (evolutionRDG (RDG_cons ass deps0) delta)
    (map (fun x : RDG => featureFamily'Aux x delta) deps0) =
    partialFeatureFamilyStep (evolutionRDG (RDG_cons ass deps0) delta)
    (map featureFamily (deps (evolutionRDG (RDG_cons ass deps0) delta)))).
    intros. rewrite H3. reflexivity. apply H''.
    assert (H''' : map (fun r : RDG => featureFamily (evolutionRDG r delta)) 
    (deps (RDG_cons ass deps0)) = map featureFamily
    (deps (evolutionRDG (RDG_cons ass deps0) delta))).
    { apply (commutativePhiEvolution _ asset). rewrite D. split;
    intros H''';discriminate H'''. }
    rewrite <- H'''. simpl. simpl in H2. apply In_map_theorem.
    apply H2.
  (*Remove Feature Case*)
  - apply In_map_theorem in H2. simpl in H2. rewrite H2.
    apply (RemoveFeatureAxiom model asset) in D. rewrite <- D.
    reflexivity.
Qed.

Theorem Phi'Equivalence {model asset :Type} `{Asset asset} `{Model model} :
  forall (m : model) (delta : RDG -> Evolution), 
  featureFamily' m delta = featureFamily (evolutionRDG (buildRDG m) delta).
Proof.
  intros. unfold featureFamily'. apply Phi'EquivalenceAux.
Qed.