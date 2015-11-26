Require Import String.
Require Import List.
Require Import Coq.Arith.EqNat.

Module Export DeBruijn.

(**
  We use a modified de Bruijn indices, which for free variables
  are a string, and for bound variables...it's the usual de Bruijn
  index.
  
  The reason this is preferable, we didn't want [lambda [x] y] to
  match [lambda [x] z], which the usual de Bruijn indices would not
  handle.
*)
Inductive Term : Type :=
  | FVar : string -> Term (* free variable *)
  | BVar : nat -> Term    (* bounded variable *)
  | Lam : Term -> Term
  | App : Term -> Term -> Term.

End DeBruijn.

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

Module PrettyTerm.

Inductive pterm : Type :=
  | Var : string -> pterm
  | Lam : string -> pterm -> pterm
  | App : pterm -> pterm -> pterm.

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
Proof. simpl. reflexivity. Qed.

Example pretty_term_2 :
  (lambda ["f", "g"] `"f") =
  PrettyTerm.Lam "f"
    (PrettyTerm.Lam "g"
      (PrettyTerm.Var "f")).
Proof. simpl. reflexivity. Qed.

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
  ((lambda [x] (PrettyTerm.Var y)) <> (lambda [x] (PrettyTerm.Var z))).
Proof.
  (* Introduce the variables, and the hypothesis
     [H : y <> z] *)
  intros.
  (* [intuition] sets us up for a proof by contradiction.
     That is, it assumes [H0 : lambda [x] `y = lambda [x] `z],
     rewrites the hypothesis as [H : y = z -> False], and
     the goal is now [False] *)
  intuition.
  (* [H : y = z -> False], the goal is now [y = z] *)
  apply H.
  (* From [H0], we have the bodies of the [lambda] expressions be equal,
     i.e., [H2 : y = z] via [inversion] *)
  inversion H0.
  (* From [H : y = z -> False] and [H2 : y = z], we get our... *)
  contradiction.
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
  apply H.
  subst.
  reflexivity.
Qed.

(** * Appendix: Helper Functions *)

(** Definitions are taken from Barendregt's _Lambda Calculus_. *)

(** The SKI combinators. Barendregt 2.1.25. *)

Module Combinator.
Definition I : Term := Lam (BVar 0).
Definition K : Term := Lam (Lam (BVar 1)).
Definition S : Term := Lam (Lam (Lam (App (App (BVar 2) (BVar 0)) (App (BVar 1) (BVar 0))))).
End Combinator.

Example s_dename_ex1 :
  dename (lambda ["x", "y", "z"] `"x" @ `"z" @ (`"y" @ `"z")) = Combinator.S.
Proof. simpl. reflexivity. Qed.


(** A term is "closed" if it has no free variables. (Barendregt, 2.1.7.ii.) *)
Fixpoint is_closed (t : Term) : Prop :=
  match t with
  | FVar s => False
  | BVar _ => True
  | Lam t' => is_closed t'
  | App t' t'' => (is_closed t') /\ (is_closed t'')
  end.

Example i_is_closed :
  is_closed Combinator.I.
Proof. reflexivity. Qed.

(** The proof for [S] being closed is deceptive, because we have to
    expand out the definition several times (due to the nested applications).
    The [constructor] tactic expands out the [is_closed] to handle
    such applications. So really, the proof is just manually unraveling
    [S].

    The trick, however, is to [simpl]-ify life. Then we our goal changes
    and we just have to prove [(True /\ True) /\ True /\ True] is [True].
    Which it is ([auto] says "No, really, it is.").
*)

Example s_is_closed :
  is_closed Combinator.S.
Proof. simpl. auto. Qed.

Example k_is_closed :
  is_closed Combinator.K.
Proof. reflexivity. Qed.

(* The collection of subterms of a given term. (Barendregt, 2.1.8.) *)
Fixpoint subterms (t : Term) : list Term :=
  match t with
  | FVar s => (FVar s)::nil
  | BVar b => (BVar b)::nil
  | Lam t' => t::(subterms t')
  | App t' t'' => cons t (app (subterms t') (subterms t''))
  end.

Example i_subterms : 
  subterms Combinator.I = Combinator.I :: (BVar 0) :: nil.
Proof. reflexivity. Qed.

Example k_subterms : 
  subterms Combinator.K = Combinator.K :: Lam (BVar 1) :: BVar 1 :: nil.
Proof. reflexivity. Qed.

Example s_subterms : 
  subterms Combinator.S = 
  Combinator.S
  :: Lam (Lam (App (App (BVar 2) (BVar 0)) (App (BVar 1) (BVar 0))))
     :: Lam (App (App (BVar 2) (BVar 0)) (App (BVar 1) (BVar 0)))
        :: App (App (BVar 2) (BVar 0)) (App (BVar 1) (BVar 0))
           :: App (BVar 2) (BVar 0)
              :: BVar 2
                 :: BVar 0
                    :: App (BVar 1) (BVar 0) :: BVar 1 :: BVar 0 :: nil.
Proof. reflexivity. Qed.

(* Barendregt 2.1.9. Modified slightly to handle the [n=0] case. *)
Fixpoint iterate (n : nat) (t : Term) : Term :=
  match n with
  | 0 => Combinator.I
  | S 0 => t
  | S n' => App t (iterate n' t)
  end.

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
