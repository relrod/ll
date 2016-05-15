Require Import List.
Import ListNotations.

(* Linear logical propositions, described by a sum type of connectives. *)
Inductive LProp : Set :=
| Implies : LProp -> LProp -> LProp
| Plus : LProp -> LProp -> LProp
| Times : LProp -> LProp -> LProp
| With : LProp -> LProp -> LProp
| One : LProp
| Top : LProp
| Zero : LProp.

(* Pretty syntax for connectives above and some other stuff below. *)
Infix "⊗" := Times (at level 76, right associativity).
Infix "⊕" := Plus (at level 76, right associativity).
Infix "&" := With (at level 76, right associativity).
Infix "⊸" := Implies (at level 76, right associativity).
Notation "a , b" := (a ++ b) (at level 76).
Notation "⊤" := Top.
Notation "⊥" := Zero.
Notation "' a" := [a] (at level 76).
Reserved Notation "a ⊢ b" (at level 76, right associativity).

(* Type alias, because :) *)
Definition Context : Set := list LProp.

(* Defining these as one massive sum type for now. In the future, consider
 * splitting them up into structural/elim/intro, like acowley did in his
 * implementation.
 *
 * Note: These are defined as per Figure 15 of
 * http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.13.8671
 * which, notably, does not include the ! and ? exponential connectives.
 * This is a future TODO.
 *)
Inductive LConsequence : (list LProp) -> LProp -> Prop :=
(* Structural rules *)
| Identity : forall (A : LProp), 'A ⊢ A
| Cut : forall (B C : LProp) (Γ Δ : Context),
    (Γ ⊢ B) -> ((Δ, 'B) ⊢ C) -> (Γ, Δ ⊢ C)
| Exchange : forall (A B C : LProp) (Γ Δ : Context),
    ((Γ, 'A, 'B, Δ) ⊢ C) -> ((Γ, 'B, 'A, Δ) ⊢ C)

(* Implication *)
| ImpliesLeft : forall (A B C : LProp) (Γ Δ : Context),
    (Γ ⊢ A) -> ((Δ ++ 'B) ⊢ C) -> ((Γ ++ Δ ++ [A ⊸ B]) ⊢ C)
| ImpliesRight : forall (A B : LProp) (Γ : Context),
    ((Γ ++ 'A) ⊢ B) -> (Γ ⊢ A ⊸ B)

(* Multiplicative Conjunction *)
| TimesLeft : forall (A B C : LProp) (Γ : Context),
    ((Γ, 'A, 'B) ⊢ C) -> ((Γ, '(A ⊗ B)) ⊢ C)
| TimesRight : forall (A B C : LProp) (Γ Δ : Context),
    (Γ ⊢ A) -> (Δ ⊢ B) -> ((Γ, Δ) ⊢ A ⊗ B)

(* Multiplicative Disjunction *)
| PlusLeft : forall (A B C : LProp) (Γ Δ : Context),
    ((Γ, 'A) ⊢ C) -> ((Γ, 'B) ⊢ C) -> ((Γ, '(A ⊕ B)) ⊢ C)
| PlusRight1 : forall (A B : LProp) (Γ : Context),
    (Γ ⊢ A) -> (Γ ⊢ (A ⊕ B))
| PlusRight2 : forall (A B : LProp) (Γ : Context),
    (Γ ⊢ B) -> (Γ ⊢ (A ⊕ B))

(* Additive Conjunction *)
| WithLeft1 : forall (A B C : LProp) (Γ : Context),
    ((Γ, 'A) ⊢ C) -> ((Γ, '(A & B)) ⊢ C)
| WithLeft2 : forall (A B C : LProp) (Γ : Context),
    ((Γ, 'B) ⊢ C) -> ((Γ, '(A & B)) ⊢ C)
| WithRight : forall (A B : LProp) (Γ : Context),
    (Γ ⊢ A) -> (Γ ⊢ B) -> (Γ ⊢ (A & B))

(* Units *)
| OneLeft : forall (C : LProp) (Γ : Context),
    (Γ ⊢ C) -> ((Γ, 'One) ⊢ C)
| OneRight : [] ⊢ One
| ZeroLeft : forall (C : LProp) (Γ : Context),
    ((Γ, 'Zero) ⊢ C)
| TopRight : forall (Γ : Context),
    Γ ⊢ ⊤
where "a ⊢ b" := (LConsequence a b).