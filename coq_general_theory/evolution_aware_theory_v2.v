Require Import Floats.
Require Import FSets.
Require Import Lists.List.

Load add.
Load zip.
Load aux_theorems.
Load formula.

Class Asset (asset : Type) : Type :=
{
  featureOperation : asset -> RatExpr;
  familyOperation : RatExpr -> list (ADD float) -> (ADD float)
}.

Inductive RDG {asset : Type} `{Asset asset} : Type :=
| RDG_leaf (ass : asset)
| RDG_cons (ass : asset) (deps : list RDG).

Inductive RDGExpressions : Type :=
| RDGE_leaf (exp : RatExpr)
| RDGE_cons (exp : RatExpr) (deps : list RDGExpressions).

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
  AddedRDG : RDG -> (RDG -> Evolution) -> RDG;
  ADDdepsRmvCase : RDG -> (RDG -> Evolution) -> list (ADD float) -> list (ADD float)
}.

(*Duas possíveis definições para phi*)

Fixpoint featureStep {asset : Type} `{Asset asset} (r : RDG) : RDGExpressions :=
  match r with
  | RDG_leaf a => RDGE_leaf (featureOperation a)
  | RDG_cons a deps => RDGE_cons (featureOperation a) (map featureStep deps)
  end.

Fixpoint familyStep {asset : Type} `{Asset asset} (r : RDGExpressions) :
  ADD float :=
  match r with
  | RDGE_leaf e => familyOperation e nil
  | RDGE_cons e deps => familyOperation e (map familyStep deps)
  end.

Definition phi {asset : Type} `{Asset asset} (r : RDG) : ADD float :=
  (familyStep (featureStep r)).

Definition phiInd' {asset : Type} `{Asset asset} (r : RDG) (l : list (ADD float)) :
  ADD float := 
  match r with
  | RDG_leaf ass => familyOperation (featureOperation ass) l
  | RDG_cons ass deps => familyOperation (featureOperation ass) l
  end.

Definition deps {asset : Type} `{Asset asset} (rdg : RDG) : list RDG :=
  match rdg with
  | RDG_leaf a => nil
  | RDG_cons a deps => deps
  end.

Axiom well_founded_In_rdg : forall (asset : Type) `{Asset asset},
  well_founded (fun r1 r2 : RDG => In r1 (deps r2)).

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

Definition Phi'Fun {model asset :Type} `{Asset asset} `{Model model}
  (mod : model) (delta : RDG -> Evolution) : ADD float := 
  Phi'Aux (buildRDG mod) delta.

(*Axioma que descreve o comportamento do phiInd' em relação ao phi.
  Utilizado para os casos em que a evolução não é ID*)

Theorem phiInd'Equivalence : forall (model asset: Type) `{Asset asset} `{Model model},
  forall (rdg : RDG),
  phiInd' rdg (map phi (deps rdg)) = phi rdg.
Proof.
  intros. destruct rdg.
  - reflexivity.
  - unfold phi. simpl. assert (H' : forall l : list RDG, 
    (map (fun r : RDG => familyStep (featureStep r)) l) = 
    (map familyStep (map featureStep l))).
    + induction l. reflexivity. simpl. rewrite IHl. reflexivity.
    + rewrite H'. reflexivity.
Qed.
(*Axioma que descreve o comportamento dos dependentes da evolução de um rdg
  cujo caso de evolução é a adição de feature*)

Axiom depsAddEvolution : forall (model asset: Type) `{Asset asset} `{Model model},
  forall (rdg : RDG) (delta : RDG -> Evolution), delta rdg = AddFeature -> 
  exists (r : RDG) (lr : list RDG), deps (evolutionRDG rdg delta) = r :: lr /\
  r = AddedRDG rdg delta /\
  lr = map (fun r : RDG => evolutionRDG r delta) (deps rdg).

(*Axioma que descreve o comportamento da evolução em um rdg que possui caso de
  evolução SubsequentModelEvol*)

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

(*Axioma que descreve o comportamento da evolução de um rdg que possui caso de
  evolução ID*)

Axiom phiInd'IDEvolution : forall (model asset: Type) `{Asset asset} `{Model model},
  forall (rdg : RDG) (delta : RDG -> Evolution), delta rdg = ID ->
  evolutionRDG rdg delta = rdg.

(*Axioma que descreve a preservação da estrutura do RDG em modelos em que a evolução
  não muda a sua estrutura*)

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
  destruct rx. reflexivity.
  (*adicionando uma hipótese que é utilizada em vários casos do
  delta rdg*)
  assert (H' : (map (fun x : RDG => Phi'Aux x delta) deps0) =
  (map phi (deps (evolutionRDG (RDG_cons ass deps0) delta))) ->
  phiInd' (evolutionRDG (RDG_cons ass deps0) delta)
  (map (fun x : RDG => Phi'Aux x delta) deps0) =
  phiInd' (evolutionRDG (RDG_cons ass deps0) delta)
  (map phi (deps (evolutionRDG (RDG_cons ass deps0) delta)))).
  { intros. rewrite H3. reflexivity. }
  destruct (delta (RDG_cons ass deps0)) eqn:D;
  simpl; rewrite D; try (apply (phiInd'IDEvolution model asset) in D; 
  rewrite D;reflexivity); rewrite <- (phiInd'Equivalence _ asset
  (evolutionRDG (RDG_cons ass deps0) delta)).
  (*Message Case*)
  - apply H'.
    assert (H'' : map (fun r : RDG => phi (evolutionRDG r delta)) 
    (deps (RDG_cons ass deps0)) = map phi 
    (deps (evolutionRDG (RDG_cons ass deps0) delta))).
    { apply (commutativePhiEvolution _ asset). rewrite D. split;
    intros H''';discriminate H'''. }
    rewrite <- H''. simpl. simpl in H2. apply In_map_theorem.
    apply H2.
  (*Presence Condition Case*)
  - apply H'.
    assert (H'' : map (fun r : RDG => phi (evolutionRDG r delta)) 
    (deps (RDG_cons ass deps0)) = map phi 
    (deps (evolutionRDG (RDG_cons ass deps0) delta))).
    { apply (commutativePhiEvolution _ asset). rewrite D. split;
    intros H''';discriminate H'''. }
    rewrite <- H''. simpl. simpl in H2. apply In_map_theorem.
    apply H2.
  (*Add Feature Case*)
  - assert (H'' :
    forall (r : RDG) (l1 l2 : list (ADD float)), l1 = l2 ->
    phiInd' r l1 = phiInd' r l2). intros. rewrite H3. reflexivity.
    apply H''. apply (depsAddEvolution model asset) in D.
    destruct D. destruct H3. destruct H3. destruct H4. rewrite H3. simpl.
    rewrite H4. assert (H''' : forall (l1 l2 : list (ADD float)) (r : ADD float),
    l1 = l2 -> r::l1 = r::l2). intros. rewrite H6. reflexivity.
    apply H'''. rewrite H5. simpl. rewrite map_phi_evolution_theorem.
    apply In_map_theorem. apply H2.
  (*Subsequent Model Evolution Case*)
  - assert (Hsub : phiInd' (RDG_cons ass deps0) 
    (map (fun x : RDG => Phi'Aux x delta) deps0) = phiInd' 
    (evolutionRDG (RDG_cons ass deps0) delta) 
    (map (fun x : RDG => Phi'Aux x delta) deps0)). 
    apply (subsequentModelAxiom _ asset). auto.
    rewrite Hsub. assert (H'' : (map (fun x : RDG => Phi'Aux x delta) deps0) =
    (map phi (deps (evolutionRDG (RDG_cons ass deps0) delta))) ->
    phiInd' (evolutionRDG (RDG_cons ass deps0) delta)
    (map (fun x : RDG => Phi'Aux x delta) deps0) =
    phiInd' (evolutionRDG (RDG_cons ass deps0) delta)
    (map phi (deps (evolutionRDG (RDG_cons ass deps0) delta)))).
    intros. rewrite H3. reflexivity. apply H''.
    assert (H''' : map (fun r : RDG => phi (evolutionRDG r delta)) 
    (deps (RDG_cons ass deps0)) = map phi 
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
  Phi'Fun m delta = phi (evolutionRDG (buildRDG m) delta).
Proof.
  intros. unfold Phi'Fun. apply Phi'EquivalenceAux.
Qed.

Require Import Strings.String.
Open Scope string_scope.

Section Example.

  Instance MensagePC : Asset (string * string) := {}.

  Definition OxigenationRDG : RDG := 
  RDG_cons ("Oxigenation","0.9970029 * rSQLite * rMemory") 
  ((RDG_leaf ("SQLite","0.998001")) :: (RDG_leaf ("Memory","0.998001")) :: nil).

  Definition deltaFunction (r : RDG) : Evolution :=
    match r with
    | RDG_leaf (a,b) => if a =? "SQLite" then Message else ID
    | RDG_cons (a,b) l => if a =? "Oxigenation" then SubsequentModelEvol else ID
    end.

  (*Exemplo de Função de Evolução*)
  Fixpoint EvolutionRDG' (delta : RDG -> Evolution) (r : RDG) : RDG :=
    match r with
    | RDG_leaf (a,b) => match delta r with
                        | ID => r
                        | Message => RDG_leaf (a,"0.555 * " ++ b)
                        | PC => RDG_leaf ("True",b)
                        | _ => r
                        end
    | RDG_cons (a,b) nil => match delta r with
                            | ID => r
                            | Message => RDG_cons (a,"0.555 * " ++ b) nil
                            | PC => RDG_cons ("True",b) nil
                            | AddFeature => RDG_cons (a,b) ((RDG_leaf ("True","1"))::nil)
                            | _ => r
                            end
    | RDG_cons (a,b) (h::t) => match delta r with
                               | ID => r
                               | Message => RDG_cons (a,"0.555 * " ++ b)
                                  (map (EvolutionRDG' delta) (h::t))
                               | PC => RDG_cons ("True",b)
                                  (map (EvolutionRDG' delta) (h::t))
                               | AddFeature => RDG_cons (a,b) 
                                  ((RDG_leaf ("True","1"))::
                                  (map (EvolutionRDG' delta) (h::t)))
                               | RemoveFeature => RDG_cons (a,b)
                                  (map (EvolutionRDG' delta) t)
                               | SubsequentModelEvol => RDG_cons (a,b)
                                  (map (EvolutionRDG' delta) (h::t))
                               end
    end.

  Theorem commutativeDepsEvolutionExample : 
    deps (EvolutionRDG' deltaFunction OxigenationRDG) = 
    map (fun r : RDG => EvolutionRDG' deltaFunction r) (deps OxigenationRDG).
  Proof.
    unfold OxigenationRDG. simpl. reflexivity.
  Qed.

End Example.




