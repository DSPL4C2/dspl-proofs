Require Import Floats.
Require Import FSets.

Load add.
Load zip.

Class RDG (rdg : Type) : Type :=
{}.

Inductive Evolution : Type :=
  | ID
  | Mensage
  | PC
  | AddFeature
  | RemoveFeature
  | SubsequentModelEvol.


Class Model (model : Type) {rdg : Type} `{RDG rdg} : Type :=
{
  buildRDG : model -> rdg;
  deps : model -> list model;
  evolutionModel : model -> (model -> Evolution) -> model;
  phi : model -> ADD float;
  phiInd' : rdg -> list (ADD float) -> ADD float
}.



Inductive phi'Rel {model rdg : Type} `{Model model} `{RDG rdg} :  model ->
(model -> Evolution) -> (ADD float) -> Prop :=
  | IDCase (m : model) (delta : model -> Evolution) 
    (H : delta m = ID \/ deps m = nil) : phi'Rel m delta (phi m)
  | MensageCase (m : model) (delta : model -> Evolution)
    (phi'deps : list (ADD float)) (H1 : delta m = Mensage) 
    (H2 : length phi'deps = length (deps m))
    (H3 : forall x : (ADD float) * model, In x (zip phi'deps (deps m)) ->
    phi'Rel (snd x) delta (fst x)) : 
    phi'Rel m delta (phiInd' (buildRDG (evolutionModel m delta))
    phi'deps)
  | PCCase (m : model) (delta : model -> Evolution)
    (phi'deps : list (ADD float)) (H1 : delta m = PC) 
    (H2 : length phi'deps = length (deps m))
    (H3 : forall x : (ADD float) * model, In x (zip phi'deps (deps m)) ->
    phi'Rel (snd x) delta (fst x)) : 
    phi'Rel m delta (phiInd' (buildRDG (evolutionModel m delta))
    phi'deps)
  | SubsequentCase (m : model) (delta : model -> Evolution)
    (phi'deps : list (ADD float)) (H1 : delta m = SubsequentModelEvol) 
    (H2 : length phi'deps = length (deps m))
    (H3 : forall x : (ADD float) * model, In x (zip phi'deps (deps m)) ->
    phi'Rel (snd x) delta (fst x)) :
    phi'Rel m delta (phiInd' (buildRDG m) phi'deps).

(*Fixpoint phi'Fun {model rdg : Type} `{Model model} `{RDG rdg} (m' : ModelInd)
(delta : model -> Evolution) : (ADD float) :=
  match m' with
  | Mod m => match delta m with
                           | ID => phi m
                           | Mensage => phiInd' (buildRDG m) (map (fun (x : model) => 
                             phi'Fun (Mod x) delta) (deps m))
                           | _ => constant 1%float
                           end
  end. *)

Theorem evolutionAnalisysEquivalenceIDCase {model rdg : Type} `{Model model} `{RDG rdg} :
  forall (m : model) (delta : model -> Evolution), delta m = ID \/
  deps (buildRDG m) = nil -> phi'Rel m delta (phi m).
Proof.
  intros. constructor. auto.
Qed.







