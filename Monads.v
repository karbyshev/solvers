Require Import FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Notations *)

Reserved Notation "x >>= f" (at level 42, left associativity).
Reserved Notation "x >>- f" (at level 42, left associativity).

(** ** Definition of monad. *)
Section axioms.
Variable T : Type -> Type.
Variable val : forall X, X -> T X.
Variable bind : forall X Y, T X -> (X -> T Y) -> T Y.
Definition val_bind := forall A B f a, @bind A B (val a) f = f a.
Definition bind_val := forall A t, @bind A A t (@val A) = t.
Definition bind_bind := forall A B C t f g, @bind B C (@bind A B t f) g = bind t (fun x => bind (f x) g).
End axioms.

Record monadType := Monad {
  T :> Type -> Type;
  tval : forall X, X -> T X;
  tbind : forall X Y, T X -> (X -> T Y) -> T Y;
  taxiom0 : @val_bind T tval tbind;
  taxiom1 : @bind_val T tval tbind;
  taxiom2 : @bind_bind T tbind
}.

(*Implicit Arguments tval[X].
Implicit Arguments tbind[X Y].*)

Notation "x >>= f" := (@tbind _ _ _ x f).

Hint Rewrite taxiom0 taxiom1 taxiom2 : monad.
Hint Extern 1 (_ = _ : T _ _) => autorewrite with monad : monad.

Ltac monad := intros; autorewrite with monad; auto with monad.

Definition map (P : monadType) X Y
  (f : X -> Y) (x : P X) : P Y :=
  x >>= (fun x => tval P (f x)).

Notation "x >>- f" := (@map _ _ _ f x).
Notation "'return' m" := ((@tval m) _) 
                            (at level 40, m ident, no associativity).

Notation "'do' X '<-' A ; B" := (@tbind _ _ _ A (fun X => B)) 
                 (at level 200, X ident, A at level 100, B at level 200).     

Section monadFacts.
Variable P : monadType.

Lemma bind_congr : forall X Y (f g : X -> P Y) (x y : P X),
  x = y -> (forall a, f a = g a) -> x >>= f = y >>= g.
Proof.
intros.
assert (E : g = f)
  by (apply functional_extensionality; auto).
now subst y g.
Qed.

Lemma unit_bind_match : forall X
  (f : X -> P X) (x : P X),
  (forall a, f a = tval P a) -> x >>= f = x.
Proof.
intros. transitivity (x >>= @tval P X).
apply bind_congr; auto.
auto with monad.
Qed.

Hint Resolve bind_congr unit_bind_match : monad.
End monadFacts.

Definition Cont (R : Type) : monadType.
exists
  (fun X => (X -> R) -> R)
  (fun X => fun x c => c x)
  (fun X Y => fun t f => fun c => t (fun x => f x c)).
- now monad.
- now monad.
- now monad.
Defined.

Definition State (S : Type) : monadType.
exists
  (fun X => S -> X * S)
  (fun X => fun x s => (x, s))
  (fun X Y => fun t f =>
    fun s => let '(x1, s1) := t s in f x1 s1).
- unfold val_bind; intuition.
- unfold bind_val. intros A t.
  extensionality s. now destruct (t s).
- unfold bind_bind. intros A B C t f g.
  extensionality s. now destruct (t s).
Defined.

Definition StateT (S : Type) (M : monadType) : monadType.
exists
  (fun X => S -> M (X * S)%type)
  (fun X => fun x s => tval _ (x,s))
  (fun X Y => fun t f =>
     fun s =>
       do p <- (t s);
       let (v,s') := p : (X * S)%type in f v s').
- unfold val_bind. intros. extensionality s. now monad.
- unfold bind_val. intros. extensionality s.
  assert (H : forall X Y Z (f : X * Y -> Z),
                (fun p => let (x,y) := p : (X * Y)%type in f (x,y)) = f)
    by (intros; extensionality p; now destruct p).
  rewrite H. now monad.
- unfold bind_bind. intros. extensionality s.
  rewrite taxiom2. f_equal. extensionality p.
  now destruct p.
Defined.

Definition Error : monadType.
exists
  (fun X => option X)
  (fun X x => Some x)
  (fun X Y t f => 
    match t with 
      | None => None
      | Some x => f x end).
- unfold val_bind; intuition.
- unfold bind_val. intros A t. now destruct t.
- unfold bind_bind. intros A B C t f g.
  destruct t; now try destruct (f a).
Defined.

Definition ErrorT (M : monadType) : monadType.
exists
  (fun X => M (option X))
  (fun X x => tval _ (Some x))
  (fun X Y t f => t >>= fun t => 
    match t with
      | None => tval _ None
      | Some x => f x end). 
- unfold val_bind; intuition.
- unfold bind_val. intros A t. apply unit_bind_match.
  intros a. now destruct a.
- unfold bind_bind. intros A B C t f g. rewrite taxiom2.
  apply bind_congr; auto.
  now destruct a; monad.
Defined.

Definition Id : monadType.
exists
  (fun X => X)
  (fun X x => x)
  (fun X Y t f => f t); easy.
Defined.
