Load model_evolution.

Fixpoint findADD (key : string) (l : list (string * (ADD float)))
  (default : ADD float) : ADD float :=
  match l with
  | nil => default
  | (s , a) :: l' => if s =? key then a else findADD key l' default
  end. 

Fixpoint func_familyOperation (re : RatExpr)
  (l : list (string * (ADD float))) : ADD float :=
  match re with
  | Const f => constant f
  | OneVar v => findADD v l (constant 1%float)
  | Sum r1 r2 => plus_add
      (func_familyOperation r1 l)
      (func_familyOperation r2 l)
  | Sub r1 r2 => sub_add
      (func_familyOperation r1 l)
      (func_familyOperation r2 l)
  | Mul r1 r2 => mult_add
      (func_familyOperation r1 l)
      (func_familyOperation r2 l)
  | Div r1 r2 => div_add
      (func_familyOperation r1 l)
      (func_familyOperation r2 l)
  | Minus r => opp_add
      (func_familyOperation r l)
  end.

Instance PC_Rat_Expr : Asset (string * RatExpr) := 
{
  familyOperation := 
    (fun ( p : string * RatExpr) (l : list (string * (ADD float))) =>
    ((fst p) , func_familyOperation (snd p) l))
}.

Definition func_featureOperation (r : RDG) : (string * RatExpr) :=
  match r with
  | RDG_leaf s p => (s , snd p)
  | RDG_cons s p l => (s , snd p)
  end.

Fixpoint RemoveVarExpr (s : string) (r : RatExpr) :=
  match r with
  | Const t => Const t
  | OneVar s' => if s' =? s then Const 1.0 else OneVar s'
  | Sum r1 r2 => Sum (RemoveVarExpr s r1) (RemoveVarExpr s r2)
  | Sub r1 r2 => Sub (RemoveVarExpr s r1) (RemoveVarExpr s r2)
  | Mul r1 r2 => Mul (RemoveVarExpr s r1) (RemoveVarExpr s r2)
  | Div r1 r2 => Div (RemoveVarExpr s r1) (RemoveVarExpr s r2)
  | Minus r => Minus (RemoveVarExpr s r)
  end.

Definition nameRDG (r : RDG) : string :=
  match r with
  | RDG_leaf s _ => s
  | RDG_cons s _ _ => s
  end.

Fixpoint Instance_EvolutionRDG (delta : RDG -> Evolution) (r : RDG) : RDG :=
  match r with
  | RDG_leaf s (pc , re) => match (delta r) with
                            | ID => r
                            | Message => RDG_leaf s (pc, Mul re (Const 0.9))
                            | PC => RDG_leaf s ("True", re)
                            | AddFeature => RDG_cons s (pc, Mul re (OneVar "AF"))
                                              ((RDG_leaf "AF" ("PCaf", Const 0.445))::nil)
                            | _ => r
                            end
  | RDG_cons s (pc , re) l => match (delta r) with
                              | ID => r
                              | Message => RDG_cons s (pc, Mul re (Const 0.9))
                                  (map (Instance_EvolutionRDG delta) l)
                              | PC => RDG_cons s ("True", re)
                                  (map (Instance_EvolutionRDG delta) l)
                              | AddFeature => RDG_cons s (pc, Mul re (OneVar "AF"))
                                         ((RDG_leaf "AF" ("PCaf", Const 0.445))::
                                          (map (Instance_EvolutionRDG delta) l))
                              | SubsequentModelEvol => RDG_cons s (pc , re)
                                    (map (Instance_EvolutionRDG delta) l)
                              | RemoveFeature => match l with
                                                 | nil => r
                                                 | h :: t => RDG_cons s 
                                                  (pc , RemoveVarExpr (nameRDG h) re)
                                                  (map (Instance_EvolutionRDG delta) t)
                                                 end
                              end
  end.

Definition Instance_ADDdepsRmvCase (r : RDG) (delta : RDG -> Evolution)
  (l : list (string * (ADD float))) : list (string * (ADD float)) :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Inductive InductiveModel : Type :=
  | Mod (r : RDG).

Axiom ID_deps_evolution : forall (r : RDG) (delta : RDG -> Evolution),
  delta r = ID -> (forall (rdg : RDG), In rdg (deps r) -> delta rdg = ID).

Theorem ID_Evolution_list : forall (delta : RDG -> Evolution) (l : list RDG),
  (forall (rdg : RDG), In rdg l -> delta rdg = ID) -> l = map (Instance_EvolutionRDG delta) l.
Proof.
  intros. induction l. auto. simpl. assert (H' : delta a = ID).
  apply H. left. reflexivity. assert (H'' : Instance_EvolutionRDG delta a = a).
  destruct a;destruct ass; unfold Instance_EvolutionRDG; rewrite H';auto.
  rewrite H''. assert (H''' : forall (r : RDG) (l1 l2 : list RDG),
  l1 = l2 -> r :: l1 = r :: l2). intros. rewrite H0. reflexivity.
  apply H'''. apply IHl. intros. apply H. right. auto.
Qed.

Program Instance InstanceModel : Model InductiveModel := 
{
  buildRDG := (fun m : InductiveModel => match m with
                                         | Mod r => r
                                         end);

  featureOperation := func_featureOperation;

  evolutionRDG := (fun (r : RDG) (d : RDG -> Evolution) =>
      Instance_EvolutionRDG d r);

  AddedRDG := (fun (r : RDG) (d : RDG -> Evolution) =>
      (RDG_leaf "AF" ("PCaf", Const 0.445)));

  ADDdepsRmvCase := Instance_ADDdepsRmvCase;
}.

{ Next Obligation.
  destruct rdg;destruct ass;
  simpl; rewrite H; simpl; exists (RDG_leaf "AF" ("PCaf", Const 0.44500000000000001)).
  - exists nil. auto.
  - exists (map (Instance_EvolutionRDG delta) deps0). auto.
Qed. }

{ Next Obligation.
  destruct rdg; destruct ass; simpl; rewrite H; auto.
Qed. }

{ Next Obligation.
  destruct rdg; destruct ass; simpl.
  - destruct (delta (RDG_leaf s (s0, r))); try (auto).
    assert (H': AddFeature = AddFeature). reflexivity. apply H in H'.
    destruct H'.
  - remember (delta (RDG_cons s (s0, r) deps0)) as delt.
    destruct delt; try auto.
    + symmetry in Heqdelt.
      assert (H' : (forall (rdg : RDG),
        In rdg (deps (RDG_cons s (s0, r) deps0)) -> delta rdg = ID)).
      apply ID_deps_evolution. auto. apply ID_Evolution_list. auto.
    + assert (H': AddFeature = AddFeature). reflexivity. apply H in H'.
      destruct H'.
    + assert (H': RemoveFeature = RemoveFeature). reflexivity. apply H0 in H'.
      destruct H'.
Qed. }




