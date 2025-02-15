import .lovelib


/-! # LoVe Homework 11: Logical Foundations of Mathematics

Homework must be done individually. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/-! ## Question 1 (9 points): Multisets as a Quotient Type

A multiset (or bag) is a collection of elements that allows for multiple
(but finitely many) occurrences of its elements. For example, the multiset
`{2, 7}` is equal to the multiset `{7, 2}` but different from `{2, 7, 7}`.

Finite multisets can be defined as a quotient over lists. We start with the
type `list α` of finite lists and consider only the number of occurrences of
elements in the lists, ignoring the order in which elements occur. Following
this scheme, `[2, 7, 7]`, `[7, 2, 7]`, and `[7, 7, 2]` would be three equally
valid representations of the multiset `{2, 7, 7}`.

The `list.count` function returns the number of occurrences of an element in a
list. Since it uses equality on elements of type `α`, it requires `α` to belong
to the `decidable_eq` type class. For this reason, the definitions and lemmas
below all take `[decidable_eq α]` as type class argument.

1.1 (1 point). Provide the missing proof below. -/

@[instance] def multiset.rel (α : Type) [decidable_eq α] : setoid (list α) :=
{ r     := λas bs, ∀x, list.count x as = list.count x bs,
  iseqv :=
    begin
      repeat { apply and.intro },
      { intros as x, refl, },
      { intros as bs h x, simp [←(h x)], },
      { intros as bs cs hab hbc x,
        simp [hab x, hbc x], }
    end }

/-! 1.2 (1 point). Define the type of multisets as the quotient over the
relation `multiset.rel`. -/

def multiset (α : Type) [decidable_eq α] : Type :=
quotient (multiset.rel α) 

/-! 1.3 (3 points). Now we have a type `multiset α` but no operations on it.
Basic operations on multisets include the empty multiset (`∅`), the singleton
multiset (`{x} `for any element `x`), and the sum of two multisets (`A ⊎ B` for
any multisets `A` and `B`). The sum should be defined so that the multiplicities
of elements are added; thus, `{2} ⊎ {2, 2} = {2, 2, 2}`.

Fill in the `sorry` placeholders below to implement the basic multiset
operations. -/

def multiset.empty {α : Type} [decidable_eq α] : multiset α :=
⟦[]⟧

def multiset.singleton {α : Type} [decidable_eq α] (a : α) : multiset α :=
⟦[a]⟧

def multiset.union {α : Type} [decidable_eq α] :
  multiset α → multiset α → multiset α :=
quotient.lift₂
  (λ as bs, ⟦as ++ bs⟧ )
  begin
    intros a₁ a₂ b₁ b₂ h₁ h₂,
    apply quotient.sound,
    intro x,
    simp [h₁ x, h₂ x],
  end

/-! 1.4 (4 points). Prove that `multiset.union` is commutative and associative,
and has `multiset.empty` as identity element. -/

lemma multiset.union_comm {α : Type} [decidable_eq α] (A B : multiset α) :
  multiset.union A B = multiset.union B A :=
begin
  apply quotient.induction_on A,
  apply quotient.induction_on B,
  intros a b,
  apply quotient.sound,
  intro x,
  simp [add_comm],
end

lemma multiset.union_assoc {α : Type} [decidable_eq α] (A B C : multiset α) :
  multiset.union (multiset.union A B) C =
  multiset.union A (multiset.union B C) :=
begin
  apply quotient.induction_on A,
  apply quotient.induction_on B,
  apply quotient.induction_on C,
  intros a b c,
  apply quotient.sound,
  intro x,
  simp [add_assoc],
end

lemma multiset.union_iden_left {α : Type} [decidable_eq α] (A : multiset α) :
  multiset.union multiset.empty A = A :=
begin
  apply quotient.induction_on A,
  intro a,
  apply quotient.sound,
  intro x,
  simp,
end

lemma multiset.union_iden_right {α : Type} [decidable_eq α] (A : multiset α) :
  multiset.union A multiset.empty = A :=
begin
  apply quotient.induction_on A,
  intro a,
  apply quotient.sound,
  intro x,
  simp,
end


/-! ## Question 2 (2 bonus points): Nonempty Types

In the lecture, we saw the inductive predicate `nonempty` that states that a
type has at least one element: -/

#print nonempty

/-! The purpose of this question is to think about what would happen if all
types had at least one element. To investigate this, we introduce this fact as
an axiom as follows. Introducing axioms should be generally avoided or done
with great care, since they can easily lead to contradictions, as we will
see. -/

axiom Sort_nonempty (α : Sort _) :
  nonempty α

/-! This axiom gives us a lemma `Sort_nonempty` admitted with no proof. It
resembles a lemma proved by `sorry`, just without the warning. -/

#check Sort_nonempty

/-! 2.1 (1 bonus point). Prove that this axiom leads to a contradiction, i.e.,
lets us derive `false`. -/

lemma proof_of_false :
  false := classical.choice (Sort_nonempty false)

/-! 2.2 (1 bonus point). Prove that even the following weaker axiom leads to a
contradiction. Of course, you may not use the axiom or the lemma from 3.1.

Hint: Subtypes can help. -/

axiom Type_nonempty (α : Type _) :
  nonempty α

lemma proof_of_false₂ :
  false := subtype.property
          (classical.choice
          (Type_nonempty
          (@subtype Type (λ_, false))))

end LoVe
