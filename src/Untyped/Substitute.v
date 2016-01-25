(** printing ==> #<span style="font-family: arial;">&rArr;</span># *)
(** printing ==>* #<span style="font-family: arial;">&rArr;*</span># *)
(** * Substitution

Lambda calculus really shines at substitution. Arguably, its entire
_raison d'être_ is to study how to substitute terms into expressions,
i.e., apply an argument to a function.

But there's a lot of subtlety here, we don't want to fall into traps.
Care must be taken when working with free variables versus
bound variables.
*)
Module Export Substitute.


Require Import String.
Require Import Coq.Arith.EqNat.
Require Import Coq.Relations.Relation_Operators.

Require Import Syntax.

(** * Capture-free substitution.

Definition (Barendregt 2.1.15). The result of substituting
[N] for [x] in [M] (denoted [[x:=N]M]) is defined as follows:
 - [[x:=N] x = N]
 - [[x:=N] y = y] (for [y <> x])
 - [[x:=N] (Lam M) = Lam ([x:=N]M)]
 - [[x:=N] (App M1 M2) = App ([x:=N]M1) ([x:=N]M2)]
*)
Reserved Notation "'[' x ':=' s ']' t" (at level 20).
(**
Substitute [s] for [x] in term [t]. There is some subtlety when
[x] is a bound variable, because we need to keep track of which
lambda it is "bound" to...this is due to using the de Bruijn
index convention.
*)
Fixpoint subst (x:Id) (s:Term) (t:Term) : Term :=
  match t with
  | FVar x' => if (eq_id_dec (FId x') x) then s else t
  | BVar n' => if (eq_id_dec (BId n') x) then s else t
  | Lam b => match x with
             | FId s' => Lam ([x:=s] b)
             | BId n => Lam ([(BId (S n)):=s] b)
             end
  | App t1 t2 => App ([x:=s] t1) ([x:=s] t2)
  end
where "'[' x ':=' s ']' t" := (subst x s t).


(**
Here are a few "helper functions" with [subst] that should
be immediately obvious. Substituting [x:=N] in [x] should
be [N], obviously.
*)
Lemma subst_free_var :
  forall (x:string) (N:Term),
  [FId x := N]FVar x = N.
Proof.
  intros.
  unfold subst. apply eq_id.
Qed.

(**
We can combine the previous results to get something
almost nontrivial. Suppose [x<>y], and [x] does not 
appear in [L]. Then substituting [[y:=L]N] for [x]
produces [[y:=L]N].
*)
Lemma unfold_one_step :
  forall (x y:string) (L N:Term),
  x<>y ->
  ~(Id_in_FV (FId x) L) ->
  [FId x := [FId y := L]N]FVar x = [FId y:=L]N.
Proof.
  intros.
  unfold subst.
  apply eq_id.
Qed.

(**
A helper lemma unfolding the definition of substitution:
Substituting [N] for a free variable in [Lam M] amounts 
to considering the lambda abstraction of substituting 
[N] for that free variable in [M].
*)
Lemma subst_lambda_swap :
  forall (x:string) (M N:Term),
  [FId x:=N]Lam M=Lam([FId x:=N]M).
Proof.
  intuition.
Qed.

(**
Another helper lemma unfolding the definition of
substitution:
Substituting [x:=N] in [M1 M2] produces the application
of substituting [x:=N] in M2 to substituting [x:=N] M1.
*) 
Lemma subst_app_functoriality :
  forall (x:string) (M1 M2 N:Term),
  [FId x:=N]App M1 M2=App ([FId x:=N]M1) ([FId x:=N]M2).
Proof.
  intuition.
Qed.

(** ** Substitution defaults to the Identity Operation

Consider this general situation [[x:=L]M] but [x] is not
a free variable in [M]. There's nothing to substitute! So
we'd expect [[x:=L]M = M], nothing should happen. We'll
present a theorem saying as much, but first we need a
couple lemmas to simplify the proof.

First, we have the case of [M] being a free variable
[y<>x]. Substitution must match the variable being 
replaced. Otherwise, it acts like the identity. And we
can prove it!
*)
Lemma subst_free_var_denied :
  forall (x y:string) (L:Term),
  x<>y -> ([FId y := L]FVar x)=FVar x.
Proof.
  intros.
  unfold subst.
  apply neq_id. (* But [FId x <> FId y] *)
  contradict H. (* If it did... *)
  inversion H.
  reflexivity.
Qed.

(**
Capture-free substitution acting on a _bound_ variable,
by definition, won't change the bound variable.
*)
Lemma subst_bvar_denied :
  forall (x:string) (n:nat) (L:Term),
  [FId x:=L]BVar n = BVar n.
Proof.
  intros.
  unfold subst. (* By definition of [subst], we see *)
  apply neq_id. (* [BId n <> FId x] *)
  discriminate. (* by looking at it! *)
Qed.

(**
Generally, substitution acts like the identity operation
on a term when we try to substitute a term for an
absent variable.

If we try to substitute [N] for [s] in [M], but [s] 
isn't in [M], then nothing happens. The substitution 
operation should return to us [M].
*)
Theorem absent_id_doesnt_subst :
  forall (s:string) (M N:Term),
  ~(Id_in_FV (FId s) M) -> [(FId s):=N]M = M.
Proof.
  intros.
  induction M.
  (* Case: M = FVar s0 *)
    rewrite subst_free_var_denied. reflexivity. apply trivial_FV_notin_FV in H. trivial.
  (* Case: M = BVar s0 *)
    unfold subst. apply neq_id. discriminate.
  (* Case: M = Lam M' *)
    rewrite subst_lambda_swap. rewrite IHM. reflexivity. auto.
  (* Case: M = App M1 M2 *)
    rewrite subst_app_functoriality. rewrite IHM1. rewrite IHM2. reflexivity.
    rewrite <- FV_app_iff in H; auto.
    rewrite <- FV_app_iff in H; auto.
Qed.

(** ** Non-Commutativity of Substitution

  The big property everyone wants to prove about substitution is
  that it's not commutative. That is to say, if we first substitute
  [x:=t1], then substitute [y:=t2], it's not the same as going the
  other way around. Why?
  
  What if [t1] has [y] in it? In order to swap the order of substitutions,
  we need to address this issue by having [y:=t2] be followed by
  [x:=[y:=t2]t1].
  
  Mathematicians have given this statement the imaginative name of...
*)

Lemma substitution_lemma_subcase_11 :
  forall (x y:string) (L M N:Term),
  x<>y /\ ~(Id_in_FV (FId x) L) ->
  [(FId y):=L]([(FId x):=N] (FVar x)) = [(FId x):=([(FId y):=L] N)]([(FId y):=L] (FVar x)).
Proof.
  intuition.
  rewrite subst_free_var; rewrite subst_free_var_denied.
  rewrite unfold_one_step. reflexivity. auto. auto. auto.
Qed.

Lemma substitution_lemma_subcase_12 :
  forall (x y:string) (L M N:Term),
  x<>y /\ ~(Id_in_FV (FId x) L) ->
  [(FId y):=L]([(FId x):=N] (FVar y)) = [(FId x):=([(FId y):=L] N)]([(FId y):=L] (FVar y)).
Proof.
  intros.
  rewrite subst_free_var; rewrite subst_free_var_denied.
  rewrite subst_free_var. rewrite absent_id_doesnt_subst. reflexivity.
  inversion H. assumption. inversion H. auto.
Qed.

Lemma substitution_lemma_subcase_13 :
  forall (x y s:string) (L M N:Term),
  x<>y -> 
  x<>s -> 
  y<>s -> 
  ~(Id_in_FV (FId x) L) ->
  [FId y := L]([FId x := N]FVar s) = [FId x := [FId y := L]N]([FId y := L]FVar s).
Proof.
  intros.
  repeat (rewrite subst_free_var_denied). (* There's nothing to substitute *)
  reflexivity. auto. auto. auto. (* so we're done *)
Qed.

(** Barendregt 2.1.16 *)
Theorem substitution_lemma : (* I didn't name it... *)
  forall (x y:string) (L M N:Term),
  x<>y -> ~(Id_in_FV (FId x) L) ->
  [(FId y):=L]([(FId x):=N] M) = [(FId x):=([(FId y):=L] N)]([(FId y):=L] M).
Proof.
  intros.
  induction M.
  (* Case: M = FVar s *)
    case (string_dec s x).
    (* Subcase: s = x *)
    - intuition.
      rewrite e. (* plugin our assumption [s = x] *) 
      apply substitution_lemma_subcase_11. auto. auto. (* and it follows from our lemma *)
    (* Subcase: s = y *)
    - case (string_dec s y).
      intros.
      rewrite e.
      apply substitution_lemma_subcase_12. auto. auto.
    (* Subcase: s <> x and s <> y *)
      intuition. apply substitution_lemma_subcase_13. auto. auto. auto. auto. auto.
  (* Case: M = BVar s *)
  - repeat (rewrite subst_bvar_denied). (* We cann't substitute [FId] for a [BVar] *)
    reflexivity. (* So we get [BVar n = BVar n], by reflexivity. *)
  (* Case: M = Lam body *)
  - repeat (rewrite subst_lambda_swap). (* We see this is true if it's true 
                                           for the body of the lambda 
                                           expressions. *)
    rewrite IHM; reflexivity. (* Then by inductive hypothesis, it's true. *)
  (* Case: M = App M1 M2 *)
  - repeat (rewrite subst_app_functoriality).
    rewrite IHM1; rewrite IHM2; reflexivity. (* Then by inductive hypothesis, it's true. *)
Qed.

(** ** Substitution in Applications

If we have [M = M'], then we have a variety of ways to substitute
[N] into this expression. 

(Barendregt 2.1.17.i) If we have [M=M'], then substituting [x:=N] to both
sides should preserve the equality.
*)
Proposition subst_apply_rand :
  forall (M M' N:Term) (x:Id),
  M=M' -> [x:=N]M = [x:=N]M'.
Proof.
  intros. rewrite H. reflexivity.
Qed.

(**
(Barendregt 2.1.17.ii) If we have [N=N'], then substituting [x:=N]
should produce the same results as substituting [x:=N'].
*)
Proposition subst_apply_rator :
  forall (M N N':Term) (x:Id),
  N=N' -> [x:=N]M = [x:=N']M.
Proof.
  intros. rewrite H. reflexivity.
Qed.

(**
(Barendregt 2.1.17.iii) The most general situation, when we have [M=M'],
and [N=N'], then substituting [[x:=N] M] should be equal to [[x:=N']M'].
*)
Proposition subst_apply_rand_rator :
  forall (M M' N N':Term) (x:Id),
  M=M' -> N=N' -> [x:=N]M = [x:=N']M'.
Proof.
  intros.
  rewrite H. rewrite H0. reflexivity.
Qed.
End Substitute.