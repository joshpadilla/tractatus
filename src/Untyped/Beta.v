Add LoadPath "./src/Untyped/".

Module src.
Module Untyped.
Module Beta.
Require Import String.
Require Import Coq.Arith.EqNat.
Require Import Coq.Relations.Relation_Operators.

Require Import Syntax.
Require Import Substitute.

(**
  Beta reduction amounts to taking a term of the form
  [(lambda x . b) t] and producing [[x:=t]b]. If the term given
  is not of this form, then return the term. In this manner, it
  acts like the identity.
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

Example i_combinator_is_identity :
  forall (t : Term),
  Beta (App Combinator.I t) = t.
Proof.
  (* unfold the definitions, then apply Id equality *)
  intuition.
  unfold Beta; unfold Combinator.I; unfold subst; apply eq_id.
Qed.

(** Definition. A term is in Beta Normal Form iff it doesn't have any
    subterms of the form [App (lambda x. body) R]. *)
Fixpoint BetaNF (M:Term) : Prop :=
  match M with
  | BVar _ => True
  | FVar _ => True
  | Lam body => BetaNF body
  | App (Lam _) _ => False
  | App M' N => (BetaNF M')/\(BetaNF N)
  end.

(** What expression wouldn't be in Beta normal form? One that would never
    terminate. For example, the [Combinator.Omega] evaluates to itself after
    beta reduction, so if we tried repeatedly beta reducing...we'll end up in
    an infinite loop. Which may be bad.
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

Notation multistep := (clos_refl_trans step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

End Beta.
End Untyped.
End src.