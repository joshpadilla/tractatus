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
We see that, for any term [t], we have 
[Combinator.I t -> t]. This merits thinking of [Combinator.I]
as the "identity function".
*)
Example i_combinator_is_identity :
  forall (t : Term),
  Beta (App Combinator.I t) = t.
Proof.
  (* unfold the definitions, then apply Id equality *)
  intuition.
  unfold Beta; unfold Combinator.I; unfold subst; apply eq_id.
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