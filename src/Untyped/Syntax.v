(* If you run into problems, try adding the following line:

Add LoadPath "~/src/tractatus/src/Untyped/".

...modify it to where the folder is, accordingly. *)

Module Export src.
Module Export Untyped.
Module Export Syntax.
Require Import String.
Require Import List.
Require Export Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Compare_dec.

(** Helper lemmas, which should be refactored into a different module.

Principle of explosion: from a contradiction, we can prove anything. 
*)
Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  inversion contra.
Qed.

Lemma list_membership :
  forall (A:Type) (x:A) (l1 l2:list A),
  (In x l1)\/(In x l2) <-> In x (l1 ++ l2).
Proof. intuition. Qed.
(* End of Helper Lemmas *)

(** * Identifiers and Variables

We treat variables and identifiers on unequal footing, depending on if they are
free or bound.
*)

Module Export Identifier.

Inductive Id : Type :=
  | FId : string -> Id (* free variable *)
  | BId : nat -> Id.   (* bounded variable *)
Hint Constructors Id.

(**
We need decidable equality on identifiers, to prove whether two [Id]s are
equal or not. These propositions establish the basic properties needed later
on.
*)
Theorem eq_id_dec : forall id1 id2 : Id, {id1 = id2} + {id1 <> id2}.
Proof.
  decide equality.
  apply string_dec.
  apply eq_nat_dec.
Qed.

Lemma eq_id : forall (T:Type) x (p q:T),
              (if eq_id_dec x x then p else q) = p.
Proof.
  intros.
  destruct (eq_id_dec x x).
  (* Case: [x=x] *)
    try reflexivity.
  (* Case: [x<>x] (impossible) *)
    apply ex_falso_quodlibet; auto.
Qed.

Lemma neq_id : forall (T:Type) x y (p q:T), x <> y ->
               (if eq_id_dec x y then p else q) = q.
Proof.
  intros.
  destruct (eq_id_dec x y).
  (* Case x = y (impossible) *)
    subst. apply ex_falso_quodlibet; apply H; reflexivity.
  (* Case x <> y *)
    reflexivity.
Qed.
End Identifier.

(** * Terms

Lambda calculus is defined, inductively, by constructing terms. A term may be:

- a variable, _x_

- a lambda abstraction ("function") λ _x_ . _M_ for some term _M_

- an application _M N_ for arbitrary terms _M_ and _N_.

Observe there are no quantifiers in the theory, since lambda calculus is an
equational theory. It is not a logical calculus. (But it can encode one!) So
any quantifiers used are purely in the metalanguage.

How do we represent a term in our metalanguage?

** De Bruijn Indices
  We use a modified de Bruijn indices, which for free variables
  are a string, and for bound variables...it's the usual de Bruijn
  index.
  
  The reason this is preferable, we didn't want [lambda [x] y] to
  match [lambda [x] z], which the usual de Bruijn indices would not
  handle.
*)
Module Export DeBruijn.

Inductive Term : Type :=
  | FVar : string -> Term (* free variable *)
  | BVar : nat -> Term    (* bounded variable *)
  | Lam : Term -> Term
  | App : Term -> Term -> Term.
Hint Constructors Term.
End DeBruijn.

(** **** Exercise

Show if [FVar s = FVar s0], then [s = s0].
*)
Lemma FVar_eq :
  forall (s s0:string),
  (FVar s0) = (FVar s) <-> s=s0.
Proof.
  intuition.
  (* -> s=s0 *)
    inversion H; reflexivity.
  (* <- (FVar s0) = (FVar s) *)
    rewrite H; reflexivity.
Qed.

(** The free variables in a term is just a list of all the free variables
    appearing in it. This is just Barendregt, definition 2.1.7.i.
*)
Fixpoint FV (t : Term) : list Term :=
  match t with
  | FVar s => (FVar s)::nil
  | BVar _ => nil
  | Lam t' => FV t'
  | App t' t'' => app (FV t') (FV t'')
  end.

(** Applying one term to another preserves the free variables in
    the representation we have chosen. Why? Because we explicitly treat
    free variables _differently_ than bound ones. Application could
    consume bound variables, but not free variables.
*)

Proposition app_FV_functorial :
  forall (M1 M2:Term),
  FV (App M1 M2) = (FV M1) ++ (FV M2).
Proof. intuition. Qed.

(** We have a property determining if an [Id] is a free variable in a term or not. 
    (Should this be an [Inductive] type instead? I'm uncertain)
*)
Definition Id_in_FV (x:Id) (t:Term) : Prop :=
  match x with
  | FId s => In (FVar s) (FV t)
  | _ => False
  end.

Lemma trivial_FV_in_FV :
  forall (s s0:string),
  Id_in_FV (FId s0) (FVar s) <-> s=s0.
Proof.
  intuition.
  (* -> *)
  inversion H. inversion H0; reflexivity. inversion H0.
  (* <- *)
  rewrite H. unfold Id_in_FV; unfold FV; compute; auto.
Qed.

Lemma trivial_FV_notin_FV :
  forall (s s0:string),
  s<>s0 <-> ~(Id_in_FV (FId s0) (FVar s)).
Proof.
  intuition.
  (* -> *)
  apply trivial_FV_in_FV in H0; contradiction.
  (* <- *)
  apply trivial_FV_in_FV in H0; contradiction.
Qed.

Corollary trivial_FV_notin_BV :
  forall (s:string) (n:nat),
  ~(Id_in_FV (FId s) (BVar n)).
Proof. intuition. Qed.

Proposition app_FV_denied_l :
  forall (s:string) (M1 M2:Term),
   (Id_in_FV (FId s) M1)\/(Id_in_FV (FId s) M2) <->
   Id_in_FV (FId s) (App M1 M2).
Proof.
  intros.
  unfold Id_in_FV; rewrite app_FV_functorial; apply list_membership.
Qed.

Module PrettyTerm.

Inductive pterm : Type :=
  | Var : string -> pterm
  | Lam : string -> pterm -> pterm
  | App : pterm -> pterm -> pterm.
Hint Constructors pterm.

End PrettyTerm.

Notation "` x" := (PrettyTerm.Var x) (at level 20).
Notation "'lambda' [ x , .. , y ] M" := (PrettyTerm.Lam x .. (PrettyTerm.Lam y M) .. ) (at level 30).
Infix "@" := PrettyTerm.App (at level 25, left associativity).

Example pretty_term_1 :
  (lambda ["f"] `"f" @ lambda ["x"] `"x" @ `"y") =
  PrettyTerm.Lam "f"
    (PrettyTerm.App
      (PrettyTerm.Var "f")
      (PrettyTerm.Lam "x"
        (PrettyTerm.App
          (PrettyTerm.Var "x")
          (PrettyTerm.Var "y")))).
Proof. reflexivity. Qed.

Example pretty_term_2 :
  (lambda ["f", "g"] `"f") =
  PrettyTerm.Lam "f"
    (PrettyTerm.Lam "g"
      (PrettyTerm.Var "f")).
Proof. reflexivity. Qed.

(** ** Syntactic Sugar: [PrettyTerm] to [Term]

  We basically want to write lambda expressions using the [PrettyTerm],
  but we want it to be converted to [DeBruijn.Term] using the "obvious"
  de Bruijn indexing notation, with the exception that free variables are
  kept as strings. (This is to prevent contradictory results --- if we
  used de Bruijn indexing convention on free variables, we'd have results like
  [lambda [x] `"y" = lambda [x] `"z"], which we don't want.)
*)

Fixpoint lookup (s: string) (ls: list (string * nat)) : option nat :=
  match ls with
  | nil => None
  | (x, n) :: t => if string_dec x s then Some n else lookup s t
  end.

(** We need to keep track of the bound variables, without adding duplicates.
    The helper function [hide] takes care of this for us.
    If the variable [s] is not in the lookup, add it associated
    to [0] (zero). This is the usual de Bruijn indexing scheme.
*)

Fixpoint hide (s: string) (ls: list (string * nat)) : list (string * nat) :=
  match ls with
  | nil => (s, 0) :: nil
  | (x, n) :: t => if string_dec x s then (x, 0) :: hide s t else (x, n + 1) :: hide s t
  end.

Fixpoint dename' (t: PrettyTerm.pterm) (binds: list (string * nat)) : Term :=
  match t with
  | PrettyTerm.Var s => match lookup s binds with
             | Some n => BVar n
             | None => FVar s
             end
  | PrettyTerm.Lam s t => Lam (dename' t (hide s binds))
  | PrettyTerm.App t1 t2 => App (dename' t1 binds) (dename' t2 binds)
  end.

Definition dename (t : PrettyTerm.pterm) : Term :=
  dename' t nil.

Coercion dename : PrettyTerm.pterm >-> Term.

(** These are basically a couple of proofs with all the
    scratchwork, and proof states, noted for the sake of
    pedagogy/pedantic-mania.
*)

(** This lemma basically says that free variables that aren't
    equal won't produce equal terms.

    The naive de Bruijn indexing scheme can't prove this, and it's
    fairly important that [lambda [x] y <> lambda [x] z] whenever [y <> z].
    (And [<>] is read as "not equals".)
*)
Lemma free_variables_dont_match_lam :
  forall (x y z : string),
  y <> z ->
  ((lambda [x] `"y") <> (lambda [x] `"z")).
Proof.
  (* Introduce the variables, and the hypothesis
     [H : y <> z] *)
  intros.
  (* [intuition] sets us up for a proof by contradiction.
     That is, it assumes [H0 : lambda [x] `y = lambda [x] `z],
     rewrites the hypothesis as [H : y = z -> False], and
     the goal is now [False] *)
  intuition.
  (* But for [H0] to hold while assuming [y = z] gives us our result. *)
  inversion H0.
Qed.

(** It is a necessary condition for the free variables of
    term [t] to be equal to the free variables of term [t'] for
    [t = t']. And we can prove it!
*)
Theorem free_var_match_necessary_cond_term_eq :
  forall (t t' : Term),
  (FV t) <> (FV t') -> t <> t'.
(* Proof by contrapositive, [H0 : t = t'] implies [FV t = FV t']. *)
Proof.
  intuition.
  apply H; subst; reflexivity.
Qed.

(** * Appendix: Helper Functions *)

(** Definitions are taken from Barendregt's _Lambda Calculus_. *)

(** The SKI combinators. Barendregt 2.1.25. We also have included the Omega combinator. *)

Module Combinator.

(** We have the classic [S], [K], and [I] combinators, which famously generate any
    closed term.
*)
Definition I : Term := Lam (BVar 0).
Hint Unfold I.
Definition K : Term := Lam (Lam (BVar 1)).
Hint Unfold K.
Definition S : Term := Lam (Lam (Lam (App (App (BVar 2) (BVar 0)) (App (BVar 1) (BVar 0))))).
Hint Unfold S.

(** We also have a nonterminating [Omega] combinator, which --- if
    evaluated --- produces itself.
*)
Definition omega : Term := App (App S I) I.
Hint Unfold omega.
Definition Omega : Term := App omega omega.
Hint Unfold Omega.

End Combinator.

Example s_dename_ex1 :
  dename (lambda ["x", "y", "z"] `"x" @ `"z" @ (`"y" @ `"z")) = Combinator.S.
Proof. simpl; reflexivity. Qed.

(** **** Closed Terms

  A term is "closed" if it has no free variables. (Barendregt, 2.1.7.ii.) 
*)
Inductive closed : Term -> Prop :=
  | fvar_closed : forall (s:string), closed (FVar s)
  | bvar_closed : forall (n:nat), closed (BVar n)
  | lam_closed : forall (t:Term), closed t -> closed (Lam t)
  | app_closed : forall (t t':Term), closed t -> closed t' -> closed (App t t').
Hint Constructors closed.

(** All combinators are closed terms. *)

Example i_is_closed :
  closed Combinator.I.
Proof. unfold Combinator.I; auto. Qed.

Example s_is_closed :
  closed Combinator.S.
Proof.
  repeat (apply lam_closed); auto.
Qed.

Example k_is_closed :
  closed Combinator.K.
Proof.
  unfold Combinator.K; auto.
Qed.

(** **** Subterms

 The collection of subterms of a given term. (Barendregt, 2.1.8.)
*)
Fixpoint subterms (t : Term) : list Term :=
  t::(match t with
      | FVar _ => nil
      | BVar _ => nil
      | Lam t' => (subterms t')
      | App t' t'' => (subterms t') ++ (subterms t'')
      end).

Example i_subterms : 
  subterms Combinator.I = Combinator.I :: (BVar 0) :: nil.
Proof. reflexivity. Qed.

Example k_subterms : 
  subterms Combinator.K = Combinator.K :: Lam (BVar 1) :: BVar 1 :: nil.
Proof. reflexivity. Qed.

Example s_subterms : 
  subterms Combinator.S = 
  Combinator.S
  :: Lam (Lam (App (App (BVar 2) (BVar 0)) 
                   (App (BVar 1) (BVar 0))))
       :: Lam (App (App (BVar 2) (BVar 0)) 
                   (App (BVar 1) (BVar 0)))
            :: App (App (BVar 2) (BVar 0)) 
                   (App (BVar 1) (BVar 0))
                 :: App (BVar 2) (BVar 0)
                      :: BVar 2 :: BVar 0
                 :: App (BVar 1) (BVar 0) 
                      :: BVar 1 :: BVar 0 
                 :: nil.
Proof. reflexivity. Qed.

(** Barendregt 2.1.9. Modified slightly to handle the [n=0] case. *)
Fixpoint iterate (n : nat) (t : Term) : Term :=
  match n with
  | 0 => Combinator.I
  | S 0 => t
  | S n' => App t (iterate n' t)
  end.

(** The length of a term is the (number of free variables) + (number of lambdas) 
    + (number of de Bruijn indices).

    Don't be fooled by the similarity between [length] and [subterms].
    It turns out the length of the list of [subterms] is not equal to the
    [length] of a term. For a counter-example, consider a term like
    [App t1 t2]. Its subterms would produce [(App t1 t2)::((Subterms t1)++(Subterms t2))].
    But its length would be [(length t1) + (length t2)].
*)
Fixpoint length (t : Term) : nat :=
  match t with
  | FVar _ => 1
  | BVar _ => 1
  | Lam t' => 1 + (length t')
  | App t' t'' => (length t') + (length t'')
  end.

Example i_length :
  length Combinator.I = 2.
Proof. reflexivity. Qed.

Example k_length :
  length Combinator.K = 3.
Proof. reflexivity. Qed.

Example s_length :
  length Combinator.S = 7.
Proof. reflexivity. Qed.


End Syntax.
End Untyped.
End src.