(** printing _beta #<span style="font-family: arial;"><sub>&beta;</sub></span># *)
(** printing beta #<span style="font-family: arial;">&beta;</span># *)
(** printing ==>beta #<span style="font-family: arial;">&rArr;<sub>&beta;</sub></span># *)
(** printing ==>beta* #<span style="font-family: arial;">&rArr;<sub>&beta;</sub>*</span># *)
(** printing ==> #<span style="font-family: arial;">&rArr;</span># *)

(** * Beta Reduction and Reduction Schemes

This is the bread-and-butter of lambda calculus. We apply
an argument to a function, that's the goal. How? We have
lambda abstractions introduce one bound variable, a "named
parameter" if you will: [λ x . M] introduces a single
variable [x].

Application is intended to _apply_ an expression to the
function. How? By _substituting_ for that bound variable,
the second expression. That is to say, [(λ x . M) N]
intuitively should "evaluate" to [[x:=N]M].

This "evaluation procedure" is called _Beta Reduction_.
We can implement it as a function...or we can think of it
as a process [(λ x . M) N -> [x:=N]M]. If we think of it
as a process, then we can form a _relation_...more like
[(λ x . M) N > [x:=N]M] which is either [True] or [False].
So, in this light, Beta reduction is a [Prop].

But how do we start reducing expressions? In something 
like [(λ x . I I I M) N], where [I] is the [I] combinator,
we could start reducing the body [I I I M -> I I M -> I M]
and so on. Or we could substitute [x:=N] to the body, then
start reducing. Does it matter? Will it produce the same
results? What if we had [(λ x . I I I M) (I I I N)]?
Can we start reducing [(I I I N) -> I I N -> I N -> N]?

The answers here are quite obviously "It doesn't matter,
they produce the same result". But that's only because we
used the identity combinator. What if we used [S] or [K]?
It's no longer immediately obvious whether we must be
careful where to start beta reducing, or whether we may
be sloppy.

What about handling paradoxical combinators like 
[Combinator.Omega] (Ω = ωω, where ω = λx. x x)? If we
tried naively to evaluate this, we'd get a nonterminating
program. That's bad. Really bad. So bad, we want to
desperately avoid this!

We'll first introduce beta reduction, then we'll discuss
various "reduction schemes" determining how to evaluate
expressions and reduce them.
*)
Require Import String.
Require Import Coq.Arith.EqNat.
Require Import Relation_Operators.

Require Import TractLib.
Require Import Syntax.
Require Import Substitute.

Module Export Beta.
(** ** Beta Reduction

Beta reduction amounts to taking a term of the form
[(lambda x . b) t] and producing [[x:=t]b]. If the term
given is not of this form, then return the term. In 
this manner, it acts like the identity.
*)

Fixpoint Beta (t:Term) : Term :=
  match t with
  | App (Lam body) t' => [(BId 0):=t']body
  | App t' t'' => match (Beta t') with
                  | (Lam body) => [(BId 0):=t'']body
                  | _ as r' => r'
                  end
  | _ => t
  end.

(**
We can see, for example, that [Combinator.I t = t] for any term [t].
And now, we can prove it!
*)
Example expand_i :
  forall (t:Term),
  (Beta (App Combinator.I t)) = t.
Proof.
  intros.
  unfold Combinator.I.
  unfold Beta.
  unfold subst.
  rewrite eq_id.
  reflexivity.
Qed.

(**
Alternatively, a more realistic treatment of beta reduction is to treat
it as a relation [t ==>_beta t']. We can axiomatize its behaviour by the
following rule of inference:

[[
   ----------------------------------------- Beta
   (App (Lam t) t') ==>_beta [(BVar 0):=t']t
]]

We can transform an application to a function by substituting in the
expression [t'] for the argument [BVar 0]. There are a few other rules
of inference which respects the structure of applications and lambda
abstractions:

[[
          t1 ==>_beta t2
    -------------------------- (B_Lam)
    (Lam t1) ==>_beta (Lam t2)

          t1 ==>_beta t2
  ------------------------------ (B_App_right)
  (App t1 x) ==>_beta (App t2 x)

          t1 ==>_beta t2
  ------------------------------ (B_App_left)
  (App x t1) ==>_beta (App x t2)
]]

Technically, this is all we need. But we work with, in practice,
the transitive, reflexive closure of beta reduction. That is to
say, we would like [t ==>_beta t] for all terms [t], and we'd like
if [t1 ==>_beta t2] and [t2 ==>_beta t3] to imply [t1 ==>_beta t3].
*)

Reserved Notation "t1 '==>_beta' t2" (at level 40).
Inductive beta : Term -> Term -> Prop :=
  | B_AppAbs : forall t1 t2,
               App (Lam t2) t1 ==>_beta [BId 0:=t1]t2
  | B_Lam : forall t1 t2,
            t1 ==>_beta t2 ->
            (Lam t1) ==>_beta (Lam t2)
  | B_App_l : forall t1 t2 t3,
              t1 ==>_beta t2 ->
              (App t3 t1) ==>_beta (App t3 t2)
  | B_App_r : forall t1 t2 t3,
              t1 ==>_beta t2 ->
              (App t1 t3) ==>_beta (App t2 t3)
where "t1 '==>_beta' t2" := (beta t1 t2).
Hint Constructors beta.

Notation multibeta := (multi beta).
Notation "t1 '==>_beta*' t2" := (multibeta t1 t2) (at level 40).

Tactic Notation "print_goal" := match goal with |- ?x => idtac x end.
Tactic Notation "normalize" := 
   repeat (print_goal; eapply multi_step ; 
             [ (eauto 10; fail) | (instantiate; simpl)]);
   apply multi_refl.

(**
We can see that [Combinator.I] acts like the identity function
when we apply any term to it. That is, [App Combinator.I t]
produces [t]. This can be made precise thanks to the beta reduction
procedure.
*)
Example i_is_id :
  forall (t:Term),
  (App Combinator.I t) ==>_beta t.
Proof.
  intro t.
  unfold Combinator.I.
  (* Rewrite the RHS of [App I t ==>_beta t] using [expand_i] *)
  rewrite <- expand_i.
  (* ... which gives us the beta reduction rule *)
  apply B_AppAbs.
Qed.

(**
If a term [t] beta reduces to [t'] in a single step, then
[t] reduces to [t'] in the multiple step version too.
(If not, there's serious problems, either in how we coded
beta reduction up, or in the logical underpinnings of our
endeavour.)
*)
Theorem multi_beta_imp : 
  forall (x y : Term),
  x ==>_beta y -> x ==>_beta* y.
Proof.
  intros x y r.
  apply multi_step with y.
  apply r. (* To prove [x ==>_beta y], use [r : x ==>beta y] as evidence *)
  apply multi_refl. (* ...and [y ==>_beta* y] by reflexivity.*)
Qed.

(**
A helper lemma we will use in a moment. Basically, we want
to show [x:=I]I=I for any variable [x].
*)
Lemma i_subst :
  forall (x:Id),
  subst x Combinator.I Combinator.I = Combinator.I.
Proof.
  intuition.
  unfold Combinator.I; unfold subst. (* Unfold the definitions *)
  induction x. (* Exhaust the cases *)
  Case "x = FId s". 
    rewrite neq_id. reflexivity. discriminate.
  Case "x = BId (S n)".
    rewrite neq_id. reflexivity. discriminate.
Qed.

(**
Now, we claim that [SII] _is_ the self-application combinator.
(Not the paradoxical, "It will blowup your computer" combinator,
but the ancillary combinator used in its definition.)
We can show that [SII] beta reduces to the self-application
combinator.
*)
Example sii_is_omega :
  (App (App Combinator.S Combinator.I) Combinator.I) ==>_beta*
  Combinator.omega.
Proof.
  unfold Combinator.S; unfold Combinator.omega. (* Unfold the definitions *)
  (* First consider [App Combinator.S Combinator.I evaluates to...] *)
  eapply multi_step. eapply B_App_r.
  (* Perform the outermost beta reduction *)
  eapply B_AppAbs. eapply multi_step.
  unfold subst; rewrite eq_id; repeat (rewrite neq_id).
  (* Perform the second beta reduction, i.e., [App (what we did) Combinator.I] *)
  eapply B_AppAbs.
  discriminate. discriminate.
  (* Perform the inner substitution
     [[BId 0 := Combinator.I]Lam (App (App Combinator.I (BVar 0)) (App (BVar 1) (BVar 0)))
     ==>_beta*
     Lam (App (BVar 0) (BVar 0))]
  *)
  unfold subst; rewrite eq_id; repeat (rewrite neq_id).
  rewrite i_subst.
  (* WTS: [Lam (App (App Combinator.I (BVar 0)) (App Combinator.I (BVar 0))) 
           ==>_beta*
           Lam (App (BVar 0) (BVar 0))] *)
  (* simplify one application of Combinator.I *)
  eapply multi_step.
  apply B_Lam; apply B_App_l; apply i_is_id.
  (* simplify the other application of Combinator.I *)
  eapply multi_step.
  apply B_Lam; apply B_App_r; apply i_is_id. 
  apply multi_refl.
  (* ...and [BId 0 <> BId 1] *)
  discriminate. 
Qed.

(**
Definition (Barendregt 2.1.34). 
A term is in Beta Normal Form iff it doesn't have any
subterms of the form [App (lambda x. body) R].
*)
Fixpoint BetaNF (M:Term) : Prop :=
  match M with
  | BVar _ => True
  | FVar _ => True
  | Lam body => BetaNF body
  | App (Lam _) _ => False
  | App M' N => (BetaNF M')/\(BetaNF N)
  end.

(**
What expression wouldn't be in Beta normal form? One that
would never terminate. For example, the [Combinator.Omega]
evaluates to itself after beta reduction, so if we tried 
repeatedly beta reducing...we'll end up in an infinite 
loop. Which may be bad.
*)
Example Omega_combinator_isnt_beta_nf :
  ~(BetaNF Combinator.Omega).
Proof.
  intros.

  unfold Combinator.Omega; (* Unfold the definitions *)
  unfold Combinator.omega;
  unfold BetaNF.

  simpl; tauto. (* And it's obvious. *)
Qed.

(**
Even unfolding the definition of [Combinator.Omega] once with
beta reduction produces [Combinator.Omega]!
*)
Example Omega_combinator_evaluates_to_itself :
  Beta Combinator.Omega = Combinator.Omega.
Proof.
  unfold Combinator.Omega; unfold Combinator.omega.
  unfold Beta. unfold subst. rewrite eq_id.
  reflexivity.
Qed.


(** * Values


We would like to think of Beta reduction as one step in an abstract
"processor". A value would be where the Beta reduction would stop after
finitely many steps. So we'll just take [BetaNF] as the criteria for
determining if a [Term] is a value or not.
*)
Definition value (t:Term) : Prop := BetaNF t.
Hint Unfold value.

(** * Small-Step Operational Semantics

We can explicitly state the rules for our "abstract processor".

*)

(** 
[[
                               value v
                      --------------------------                    (ST_AppAbs)
                        (λx.t) v ==> [x:=v]t

                              t1 ==> t1'
                           ----------------                           (ST_App1)
                           t1 t2 ==> t1' t2

                              value v
                              t2 ==> t2'
                            --------------                           (ST_App2)
                            v t2 ==> v t2'
]]
*)
Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : Term -> Term -> Prop :=
  | ST_AppAbs : forall t v,
         value v ->
         (App (Lam t) v) ==> [BId 0:=v]t (* Beta reduction, more or less *)
  | ST_App1 : forall t1 t1' t2,
         t1 ==> t1' ->
         App t1 t2 ==> App t1' t2
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 ==> t2' ->
         App v1 t2 ==> App v1 t2'
where "t1 '==>' t2" := (step t1 t2).
Hint Constructors step.


Notation multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

Example Omega_steps_to_itself:
  Combinator.Omega ==>* Combinator.Omega.
Proof.
  apply multi_refl.
Qed.
End Beta.