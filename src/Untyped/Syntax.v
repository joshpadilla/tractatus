Module Export Syntax.
Require Import String.
Require Import List.
Require Export Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Compare_dec.
Require Import TractLib.

(** * Introduction: Lambda Calculus

Lambda calculus is the smallest complete programming language in the world.
We can perform, really, two operations: (1) form functions, (2) apply 
arguments to functions.

We'll construct the basic abstract syntax tree for untyped lambda calculus,
then develop other mechanisms in other files.

The basic concept for untyped lambda calculus is the "expression" or "term",
which can be an "identifier", a "function", or an "application". Lets 
first develop the framework for "names" (or "identifiers").
*)

(** * Identifiers and Variables

For lambda calculus, identifiers are used to...identify...variables. And
variables are only used as parameters in functions. They do not store
values, as they would in modern programming languages.

We treat both variables, and identifiers, on unequal footing...in the sense
that we specify if they are free or bound.
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
  Case "x=x".
    try reflexivity.
  Case "x<>x". (* impossible *)
    apply ex_falso_quodlibet; auto.
Qed.

Lemma neq_id : forall (T:Type) x y (p q:T), x <> y ->
               (if eq_id_dec x y then p else q) = q.
Proof.
  intros.
  destruct (eq_id_dec x y).
  Case "x=y". (* impossible *)
    subst. apply ex_falso_quodlibet; apply H; reflexivity.
  Case "x <> y". reflexivity.
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

The grammar for this can be written quite quickly in BNF:

<<
<term> ::= <variable>
         | 'λ' <variable> '.' <term>
         | <term> <term>
>>

The problem is...How do we represent a term in our metalanguage?

** De Bruijn Indices

Suppose all variables are "bound", meaning they first show up in
a lambda expression defining it. The only way to introduce a variable
[x] is to write [λ x . M] for some [M]. One trick, credited to
Niklaus de Bruijn (prenounced "de Browne"), is to use numbers for
bound variables. This makes it easy to determine if a variable is
free or bound, and substitution just looks for the proper number.

There's more to this trick, however. The number we give to a bound
variable is "How 'deeply nested' the variable is, from its declaration."
Lets give a couple of examples to illustrate what this means.

- Consider [λx. λy. x].
  - Since we have only 1 bound variable [x] in the body of the
    our second lambda expression, we have to replace it with a 
    number. And since it's bound to the _first_ lambda expression,
    one layer above where it's used (that's the important bit), we
    replace it with [1]. The de Bruijn indices then kill off the
    variables in the declaration, since they're now represented by
    numbers, giving us [λλ1].
  - If we had instead [λx. λy. y], then it would be [λλ0] since [y]
    is used in the body of the lambda where it is declared.
- Consider [λx. λy. λz. x z (y z)].
  - Starting with the innermost lambda abstraction, we see [z] is used
    in the body of the lambda declaring it. We can replace it with
    [λx. λy. λ(x 0 (y 0))].
  - Next, we have the [y] variable to replace. Since it is declared one
    abstraction _above_ the body of the lambda where it is used, we
    replace it with [1], giving us [λx. λλ. (x 0 (1 0))].
  - Lastly, we have [x], which is declared 2 layers above the body
    where it is used. So we replace it with [2]: [λλλ. (2 0 (1 0))].


Our discussion so far has been concerning variables first declared
in a lambda expression, i.e., "bound" variables. What if the user
puts in variables _not_ "bound" to a lambda expression? For example,
[λ x . z], what happens to [z] ("free variables")?

We use a modified de Bruijn indices, which for free variables
are a string, and for bound variables...it's the usual de Bruijn
index.
  
The reason this is preferable, we didn't want [lambda [x] y] to
match [lambda [x] z], which the usual de Bruijn indices would not
handle...at least, not without some _global_ notion of which variables 
have been "used up" and which ones are "fresh".
*)
Module Export DeBruijn.

Inductive Term : Type :=
  | FVar : string -> Term (* free variable *)
  | BVar : nat -> Term    (* bounded variable *)
  | Lam : Term -> Term
  | App : Term -> Term -> Term.
Hint Constructors Term.
End DeBruijn.

(**
This crops up later, but it's useful to know if a given term is an abstraction
("function") or not.
*)
Definition is_abs (t:Term) : Prop :=
  match t with
  | Lam _ => True
  | _ => False
  end.

(**
For the sake of completeness, we'll also provide predicates for if a term is a
variable, an application, etc.
*)
Definition is_var (t:Term) : Prop :=
  match t with
  | FVar _ => True
  | BVar _ => True
  | _ => False
  end.

Definition is_free_var (t:Term) : Prop :=
  match t with
  | FVar _ => True
  | _ => False
  end.

Definition is_app (t:Term) : Prop :=
  match t with
  | App _ _ => True
  | _ => False
  end.

(** **** Exercise

Show if [FVar s = FVar s0], then [s = s0].
*)
Lemma FVar_eq :
  forall (s s0:string),
  (FVar s0) = (FVar s) <-> s=s0.
Proof.
(* Left for the reader ;) *)
(* begin hide *)
  intuition.
  Case "s=s0". inversion H; reflexivity.
  Case "(FVar s0) = (FVar s)". rewrite H; reflexivity.
(* end hide *)
Qed.

(**
The free variables in a term is just a list of all the free variables
appearing in it. We have a function [FV] to obtain this list!
This is just Barendregt, definition 2.1.7.i.
*)
Fixpoint FV (t : Term) : list Term :=
  match t with
  | FVar s => (FVar s)::nil
  | BVar _ => nil
  | Lam t' => FV t'
  | App t' t'' => app (FV t') (FV t'')
  end.

(**
*** Exercise
Show that [forall (v t:Term), In v (FV t) -> is_free_var v].
*)

(**
*** Helper Functions

Applying one term to another preserves the free variables in
the representation we have chosen. Why? Because we explicitly treat
free variables _differently_ than bound ones. Application could
consume bound variables, but not free variables.

_Remark_. 
Note that "functorial" is used loosely. Although, I suppose one
could make the argument it's a "functor" from the [tree] underlying
the Abstract Syntax Tree, to the [list] of free variables, preserving
concatenation. But it's not an honest, mathematical functor!
*)

Proposition app_FV_functorial :
  forall (M1 M2:Term),
  FV (App M1 M2) = app (FV M1) (FV M2).
Proof. intuition. Qed.

(**
We have a property determining if an [Id] is a free variable in a term or not. 
(Should this be an [Inductive] type instead? I'm uncertain)
*)
Definition Id_in_FV (x:Id) (t:Term) : Prop :=
  match x with
  | FId s => In (FVar s) (FV t)
  | _ => False
  end.

(**
Let [x] is a free variable. 

The identifier [i] is in [FV(x)] 
if and only if
the string representation of [x] _is_ the string representation of [i].
*) 
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

(**
The converse is also true.
*)
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

(**
And it follows that if [x] is a bound variable, then no free variable could
ever hope to be in [FV(x)]...because [FV(x)] is [nil].
*)
Corollary trivial_FV_notin_BV :
  forall (s:string) (n:nat),
  ~(Id_in_FV (FId s) (BVar n)).
Proof. intuition. Qed.

Proposition FV_app_iff :
  forall (s:string) (M1 M2:Term),
   (Id_in_FV (FId s) M1)\/(Id_in_FV (FId s) M2) <->
   Id_in_FV (FId s) (App M1 M2).
Proof.
  intros.
  unfold Id_in_FV; rewrite app_FV_functorial; rewrite in_app_iff; reflexivity.
Qed.
Qed.

(** * A Prettier Syntax

We allow a user to write a more palatable version of lambda calculus, which we then
transform into our abstract syntax tree representation.

*)

Module PrettyTerm.

Inductive pterm : Type :=
  | Var : string -> pterm
  | Lam : string -> pterm -> pterm
  | App : pterm -> pterm -> pterm.
Hint Constructors pterm.

End PrettyTerm.

Notation "` x" := (PrettyTerm.Var x) (at level 20).
Notation "x '~>' M" :=  (PrettyTerm.Lam x M) (at level 30).
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
used de Bruijn indexing convention on free variables, we'd have results 
like [lambda [x] `"y" = lambda [x] `"z"], which we don't want.)
*)

Fixpoint lookup (s: string) (ls: list (string * nat)) : option nat :=
  match ls with
  | nil => None
  | (x, n) :: t => if string_dec x s then Some n else lookup s t
  end.

(**
We need to keep track of the bound variables, without adding duplicates.
The helper function [hide] takes care of this for us.
If the variable [s] is not in the lookup, add it associated
to [0] (zero). This is the usual de Bruijn indexing scheme.
*)

Fixpoint hide (s: string) (ls: list (string * nat)) : list (string * nat) :=
  match ls with
  | nil => (s, 0) :: nil
  | (x, n) :: t => if string_dec x s then (x, 0) :: hide s t else (x, n + 1) :: hide s t
  end.

(**
We take a pretty term and a list of bindings, and recursively
translate to the internal abstract syntax tree representation for the
expression.
*)
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

(**
These are basically a couple of proofs with all the
scratchwork, and proof states, noted for the sake of
pedagogy/pedantic-mania.

This lemma basically says that free variables that aren't
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
     [H : y <> z]. Here, [intuition] sets us up for a proof 
     by contradiction. That is, it assumes 
     [H0 : lambda [x] `y = lambda [x] `z],
     rewrites the hypothesis as [H : y = z -> False], and
     the goal is now [False] *)
  intuition.
  (* But for [H0] to hold while assuming [y = z] gives us our result. *)
  inversion H0.
Qed.

(**
It is a necessary condition for the free variables of
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

(** ** Combinators

**** Definition

A _Combinator_ is a term with no free variables, only bound variables.

**** SKI Combinators and Friends

The SKI combinators. Barendregt 2.1.25.

There is a folklore theorem stating any combinator may be written in
terms of SKI combinators...which explains their importance.

We also have included the Omega combinator, which paradoxically evaluates to itself.
*)

Module Combinator.

(**
We have the classic [S], [K], and [I] combinators, which famously generate any
closed term. Recall:

- [I = λx. x] is the identity combinator,

- [K = λx. λy. y] is the constant combinator

- [S = λx. λy. λz. x z (y z)] a generalized application.
*)
Definition I : Term := Lam (BVar 0).
Definition K : Term := 
  Lam (Lam (BVar 1)).
Definition S : Term := (* λx. λy. λz. x z (y z) *)
  Lam (Lam (Lam (App (App (BVar 2) (BVar 0)) (App (BVar 1) (BVar 0))))).


(**
We have the application combinator [omega] (ω = λx. x x).
We also have a nonterminating [Omega] (Ω) combinator, which --- if
evaluated --- produces itself.
*)
Definition omega : Term := Lam (App (BVar 0) (BVar 0)).
Definition Omega : Term := App omega omega.

End Combinator.

Lemma omega_is_abs :
  is_abs Combinator.omega.
Proof.
reflexivity.
Qed.

Example s_dename_ex1 :
  dename (lambda ["x", "y", "z"] `"x" @ `"z" @ (`"y" @ `"z")) = Combinator.S.
Proof. simpl; reflexivity. Qed.

(** *** Closed Terms

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

(** *** Subterms

(Barendregt, 2.1.8.) The collection of subterms of a given term. Variables
have no subterms except themselves: they're as simple as we can get.

A lambda expression has a body, so the expression plus subterms of the body
produces the subterms for the expression as a whole.

Similarly, application takes two arguments, so their subterms plus the
expression produces the subterms for the application expression.
*)
Fixpoint subterms (t : Term) : list Term :=
  match t with
  | FVar _ => t::nil
  | BVar _ => t::nil
  | Lam t' => t::(subterms t')
  | App t' t'' => t::(app (subterms t') (subterms t''))
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

(** **** Iterative Applications

Barendregt 2.1.9. If we write, say, [M^n N], we should understand this means
[M M M ... M N] where [M] has been repeated [n] times. We have a function for that,
writing [M^n N = App (iterate n M) N]. Our definitions modifies Barendregt's
slightly to handle the [n=0] case. 
*)
Fixpoint iterate (n : nat) (t : Term) : Term :=
  match n with
  | 0 => Combinator.I
  | S 0 => t
  | S n' => App t (iterate n' t)
  end.

(** **** Term Length

The length of a term is the (number of free variables) + (number of lambdas) 
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

(** * References

- Barendregt, _The Lambda Calculus, Its Syntax and Semantics_.
- Stanford Encyclopedia of Philosophy entry, http://plato.stanford.edu/entries/lambda-calculus/
- Raul Rojas, "A Tutorial Introduction to the Lambda Calculus".
*)