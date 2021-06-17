Require Import Floats.
Require Import FSets.
Require Import Lists.List.

Load add.
Load zip.
Load aux_theorems.

Class Asset (asset : Type) : Type :=
{}.

Inductive RDG {asset : Type} `{Asset asset} : Type :=
| RDG_leaf (ass : asset)
| RDG_cons (ass : asset) (deps : list RDG).

Inductive Evolution : Type :=
  | ID
  | Message
  | PC
  | AddFeature
  | SubsequentModelEvol
  | RemoveFeature.

Class Model (model : Type) {asset : Type} `{Asset asset} : Type :=
{
  buildRDG : model -> RDG;
  evolutionRDG : RDG -> (RDG -> Evolution) -> RDG;
  phi : RDG -> ADD float;
  phiInd' : RDG -> list (ADD float) -> ADD float;
  AddedRDG : RDG -> (RDG -> Evolution) -> RDG;
  ADDdepsRmvCase : RDG -> (RDG -> Evolution) -> list (ADD float) -> list (ADD float);
}.

Definition deps {asset : Type} `{Asset asset} (rdg : RDG) : list RDG :=
  match rdg with
  | RDG_leaf a => nil
  | RDG_cons a deps => deps
  end.

Fixpoint Phi'Aux {model asset :Type} {H1 : Asset asset} {H2 : Model model}
  (rdg : RDG) (delta : RDG -> Evolution) : (ADD float) := 
  match rdg with
  | RDG_leaf a => phi (evolutionRDG rdg delta)
  | RDG_cons a deps => match (delta rdg) with
                       | ID => phi rdg
                       | Message => phiInd' (evolutionRDG rdg delta)
                          (map (fun (x : RDG) => Phi'Aux (x) delta) deps)
                       | PC => phiInd' (evolutionRDG rdg delta)
                          (map (fun (x : RDG) => Phi'Aux (x) delta) deps)
                       | SubsequentModelEvol => phiInd' rdg
                          (map (fun (x : RDG) => Phi'Aux (x) delta) deps)
                       | AddFeature => phiInd' (evolutionRDG rdg delta)
                          ((phi (AddedRDG rdg delta))::(map
                          (fun (x : RDG) => Phi'Aux (x) delta) deps))
                       (*O coq estava reclamando da recursão ao 
                         aplicar uma função nos deps, então foi preciso
                         ajustar a função RemoveADDdeps para mudar a lista de ADDs,
                         e não a lista de RDG*)
                       | RemoveFeature => phiInd' (evolutionRDG rdg delta)
                          (ADDdepsRmvCase rdg delta 
                          (map (fun (x : RDG) => Phi'Aux (x) delta) deps))
                       end
  end.
(*Outra modelagem para a função Phi'. Nessa modelagem, o delta utilizado no
  map dos casos Mensage,PC,Add e Remove é o delta que sempre retorna o ID, tornando
  a nossa modelagem menos genérica mas ainda de acordo com os nossos casos de 
  evolução. Essa mudança pode ser utilizada para auxiliar na prova de propriedades
  envolvendo os dependentes da evolução de um RDG*)
(*
Fixpoint Phi'Aux' {model asset :Type} {H1 : Asset asset} {H2 : Model model}
  (rdg : RDG) (delta : RDG -> Evolution) : (ADD float) :=
  match rdg with
  | RDG_leaf a => phi (evolutionRDG rdg delta)
  | RDG_cons a deps => match (delta rdg) with
                       | ID => phi rdg
                       | Message => phiInd' (evolutionRDG rdg delta)
                          (map (fun (x : RDG) => Phi'Aux (x) 
                          (fun r : RDG => ID)) deps)
                       | PC => phiInd' (evolutionRDG rdg delta)
                          (map (fun (x : RDG) => Phi'Aux (x) 
                          (fun r : RDG => ID)) deps)
                       | SubsequentModelEvol => phiInd' rdg
                          (map (fun (x : RDG) => Phi'Aux (x) delta) deps)
                       | AddFeature => phiInd' (evolutionRDG rdg delta)
                          ((phi (AddedRDG rdg delta))::(map
                          (fun (x : RDG) => Phi'Aux (x) (fun r : RDG => ID)) deps))
                       (*O coq estava reclamando da recursão ao 
                         aplicar uma função nos deps, então foi preciso
                         ajustar a função RemoveADDdeps para mudar a lista de ADDs,
                         e não a lista de RDG*)
                       | RemoveFeature => phiInd' (evolutionRDG rdg delta)
                          (RemoveADDdeps rdg delta 
                          (map (fun (x : RDG) => Phi'Aux (x) 
                          (fun r : RDG => ID)) deps))
                       end
  end.*)

Definition Phi'Fun {model asset :Type} `{Asset asset} `{Model model}
  (mod : model) (delta : RDG -> Evolution) : ADD float := 
  Phi'Aux (buildRDG mod) delta.

Axiom phiInd'Equivalence : forall (model asset: Type) `{Asset asset} `{Model model},
  forall (rdg : RDG),
  phiInd' rdg (map phi (deps rdg)) = phi rdg.

Axiom depsAddEvolution : forall (model asset: Type) `{Asset asset} `{Model model},
  forall (rdg : RDG) (delta : RDG -> Evolution), delta rdg = AddFeature -> 
  exists (r : RDG) (lr : list RDG), deps (evolutionRDG rdg delta) = r :: lr /\
  r = AddedRDG rdg delta /\
  lr = map (fun r : RDG => evolutionRDG r delta) (deps rdg).

Axiom subsequentModelAxiom : forall (model asset: Type) `{Asset asset} 
  `{Model model}, forall (r : RDG) (delta : RDG -> Evolution)
  (l : list (ADD float)), delta r = SubsequentModelEvol -> 
  phiInd' r l = phiInd' (evolutionRDG r delta) l.

(*Procurar redução para esse axioma*)

Axiom RemoveFeatureAxiom : forall (model asset: Type) `{Asset asset} 
  `{Model model}, forall (r : RDG) (delta : RDG -> Evolution),
  delta r = RemoveFeature -> 
  ADDdepsRmvCase r delta (map (fun rdg : RDG => phi (evolutionRDG rdg delta))
  (deps r)) = map phi (deps (evolutionRDG r delta)).

Axiom phiInd'IDEvolution : forall (model asset: Type) `{Asset asset} `{Model model},
  forall (rdg : RDG) (delta : RDG -> Evolution), delta rdg = ID ->
  evolutionRDG rdg delta = rdg.

(*Definir Exemplo e tentar reduzir*)

Axiom commutativeDepsEvolution : forall (model asset: Type) `{Asset asset} `{Model model},
  forall (rdg : RDG) (delta : RDG -> Evolution) , delta rdg <> AddFeature /\
  delta rdg <> RemoveFeature -> deps (evolutionRDG rdg delta) =
  map (fun r : RDG => evolutionRDG r delta) (deps rdg).

Theorem commutativePhiEvolution : forall (model asset: Type) `{Asset asset} `{Model model},
  forall (rdg : RDG) (delta : RDG -> Evolution) , delta rdg <> AddFeature /\
  delta rdg <> RemoveFeature ->
   map (fun r : RDG => phi (evolutionRDG r delta)) (deps rdg) = 
   map phi (deps (evolutionRDG rdg delta)).
Proof.
  intros. assert (H' : forall (l : list RDG) (d : RDG -> Evolution),
  map (fun r : RDG => phi (evolutionRDG r d)) l = map phi (map 
  (fun r : RDG => evolutionRDG r d) l)).
  { induction l.
    - intros. reflexivity.
    - intros. simpl. rewrite IHl. reflexivity. }
  rewrite H'. apply (commutativeDepsEvolution model asset) in H2.
  rewrite H2. reflexivity.
Qed.

Axiom well_founded_In_rdg : forall (asset : Type) `{Asset asset},
  well_founded (fun r1 r2 : RDG => In r1 (deps r2)).

Theorem well_founded_phi_equivalence {model asset :Type} 
  `{Asset asset} `{Model model} : forall delta : RDG -> Evolution,
  (forall rx : RDG, (forall ry : RDG,
  (fun r1 r2 : RDG => In r1 (deps r2)) ry rx -> 
  (fun r : RDG => Phi'Aux r delta = phi (evolutionRDG r delta)) ry) ->
  (fun r : RDG => Phi'Aux r delta = phi (evolutionRDG r delta)) rx) ->
  forall r : RDG, (fun r : RDG => Phi'Aux r delta = phi (evolutionRDG r delta)) r.
Proof.
  intros delta. apply well_founded_ind. apply well_founded_In_rdg.
Qed.

Theorem map_phi_evolution_theorem {model asset :Type} 
  `{Asset asset} `{Model model} : forall (delta : RDG -> Evolution)
  (l : list RDG), map phi (map (fun r : RDG => evolutionRDG r delta) l) = 
  map (fun r : RDG => phi (evolutionRDG r delta)) l.
Proof. 
  intros. induction l.
  - reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

Theorem Phi'EquivalenceAux {model asset :Type} `{Asset asset} `{Model model} :
  forall (rdg : RDG) (delta : RDG -> Evolution),
  Phi'Aux rdg delta = phi (evolutionRDG rdg delta).
Proof.
  intros. apply well_founded_phi_equivalence. intros.
  destruct rx. reflexivity. destruct (delta (RDG_cons ass deps0)) eqn:D.
  - simpl. rewrite D. apply (phiInd'IDEvolution model asset) in D. rewrite D.
    reflexivity.
  - simpl. rewrite D. rewrite <- (phiInd'Equivalence _ asset).
    assert (H' : (map (fun x : RDG => Phi'Aux x delta) deps0) =
    (map phi (deps (evolutionRDG (RDG_cons ass deps0) delta))) ->
    phiInd' (evolutionRDG (RDG_cons ass deps0) delta)
    (map (fun x : RDG => Phi'Aux x delta) deps0) =
    phiInd' (evolutionRDG (RDG_cons ass deps0) delta)
    (map phi (deps (evolutionRDG (RDG_cons ass deps0) delta)))).
    intros. rewrite H3. reflexivity. apply H'.
    assert (H'' : map (fun r : RDG => phi (evolutionRDG r delta)) 
    (deps (RDG_cons ass deps0)) = map phi 
    (deps (evolutionRDG (RDG_cons ass deps0) delta))).
    { apply (commutativePhiEvolution _ asset). rewrite D. split;
    intros H''';discriminate H'''. }
    rewrite <- H''. simpl. simpl in H2. apply In_map_theorem.
    apply H2.
  - simpl. rewrite D. rewrite <- (phiInd'Equivalence _ asset).
    assert (H' : (map (fun x : RDG => Phi'Aux x delta) deps0) =
    (map phi (deps (evolutionRDG (RDG_cons ass deps0) delta))) ->
    phiInd' (evolutionRDG (RDG_cons ass deps0) delta)
    (map (fun x : RDG => Phi'Aux x delta) deps0) =
    phiInd' (evolutionRDG (RDG_cons ass deps0) delta)
    (map phi (deps (evolutionRDG (RDG_cons ass deps0) delta)))).
    intros. rewrite H3. reflexivity. apply H'.
    assert (H'' : map (fun r : RDG => phi (evolutionRDG r delta)) 
    (deps (RDG_cons ass deps0)) = map phi 
    (deps (evolutionRDG (RDG_cons ass deps0) delta))).
    { apply (commutativePhiEvolution _ asset). rewrite D. split;
    intros H''';discriminate H'''. }
    rewrite <- H''. simpl. simpl in H2. apply In_map_theorem.
    apply H2.
  - simpl. rewrite D. rewrite <- (phiInd'Equivalence _ asset
    (evolutionRDG (RDG_cons ass deps0) delta)). assert (H' :
    forall (r : RDG) (l1 l2 : list (ADD float)), l1 = l2 ->
    phiInd' r l1 = phiInd' r l2). intros. rewrite H3. reflexivity.
    apply H'. apply (depsAddEvolution model asset) in D.
    destruct D. destruct H3. destruct H3. destruct H4. rewrite H3. simpl.
    rewrite H4. assert (H'' : forall (l1 l2 : list (ADD float)) (r : ADD float),
    l1 = l2 -> r::l1 = r::l2). intros. rewrite H6. reflexivity.
    apply H''. rewrite H5. simpl. rewrite map_phi_evolution_theorem.
    apply In_map_theorem. apply H2.
  - simpl. rewrite D. rewrite <- (phiInd'Equivalence _ asset).
    assert (Hsub : phiInd' (RDG_cons ass deps0) 
    (map (fun x : RDG => Phi'Aux x delta) deps0) = phiInd' 
    (evolutionRDG (RDG_cons ass deps0) delta) 
    (map (fun x : RDG => Phi'Aux x delta) deps0)). 
    apply (subsequentModelAxiom _ asset). auto.
    rewrite Hsub. assert (H' : (map (fun x : RDG => Phi'Aux x delta) deps0) =
    (map phi (deps (evolutionRDG (RDG_cons ass deps0) delta))) ->
    phiInd' (evolutionRDG (RDG_cons ass deps0) delta)
    (map (fun x : RDG => Phi'Aux x delta) deps0) =
    phiInd' (evolutionRDG (RDG_cons ass deps0) delta)
    (map phi (deps (evolutionRDG (RDG_cons ass deps0) delta)))).
    intros. rewrite H3. reflexivity. apply H'.
    assert (H'' : map (fun r : RDG => phi (evolutionRDG r delta)) 
    (deps (RDG_cons ass deps0)) = map phi 
    (deps (evolutionRDG (RDG_cons ass deps0) delta))).
    { apply (commutativePhiEvolution _ asset). rewrite D. split;
    intros H''';discriminate H'''. }
    rewrite <- H''. simpl. simpl in H2. apply In_map_theorem.
    apply H2.
  - simpl. rewrite D. rewrite <- (phiInd'Equivalence _ asset).
    apply In_map_theorem in H2. simpl in H2. rewrite H2.
    apply (RemoveFeatureAxiom model asset) in D. rewrite <- D.
    reflexivity.
Qed.

Theorem Phi'Equivalence {model asset :Type} `{Asset asset} `{Model model} :
  forall (m : model) (delta : RDG -> Evolution), 
  Phi'Fun m delta = phi (evolutionRDG (buildRDG m) delta).
Proof.
  intros. unfold Phi'Fun. apply Phi'EquivalenceAux.
Qed.





