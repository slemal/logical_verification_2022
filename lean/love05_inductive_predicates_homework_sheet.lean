import .lovelib


/-! # LoVe Homework 5: Inductive Predicates

Homework must be done individually. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/-! ## Question 1 (3 points): A Type of λ-Terms

Recall the following type of λ-terms from question 3 of exercise 4: -/

inductive term : Type
| var : string → term
| lam : string → term → term
| app : term → term → term

/-! 1.1 (1 point). Define an inductive predicate `is_app` that returns `true` if
its argument is of the form `term.app …` and that returns false otherwise. -/

inductive is_app : term → Prop
| app : ∀t u, is_app (term.app t u)

/-! 1.2 (2 points). Define an inductive predicate `is_abs_free` that is true if
and only if its argument is a λ-term that contains no λ-expressions. -/

inductive is_abs_free : term → Prop
| app : ∀t u, is_abs_free t → is_abs_free u → is_abs_free (term.app t u)
| var : ∀s, is_abs_free (term.var s)


/-! ## Question 2 (6 points): Even and Odd

Consider the following inductive definition of even numbers: -/

inductive even : ℕ → Prop
| zero            : even 0
| add_two {n : ℕ} : even n → even (n + 2)

/-! 2.1 (1 point). Define a similar predicate for odd numbers, by completing the
Lean definition below. The definition should distinguish two cases, like `even`,
and should not rely on `even`. -/

inductive odd : ℕ → Prop
| one             : odd 1
| add_two {n : ℕ} : odd n → odd (n + 2)

/-! 2.2 (1 point). Give proof terms for the following propositions, based on
your answer to question 2.1. -/

lemma odd_3 :
  odd 3 :=
begin
  apply odd.add_two,
  exact odd.one,
end

lemma odd_5 :
  odd 5 :=
begin
  apply odd.add_two,
  exact odd_3,
end

/-! 2.3 (2 points). Prove the following lemma by rule induction, as a "paper"
proof. This is a good exercise to develop a deeper understanding of how rule
induction works (and is good practice for the final exam).

    lemma even_odd {n : ℕ} (heven : even n) :
      odd (n + 1) :=

Guidelines for paper proofs:

We expect detailed, rigorous, mathematical proofs. You are welcome to use
standard mathematical notation or Lean structured commands (e.g., `assume`,
`have`, `show`, `calc`). You can also use tactical proofs (e.g., `intro`,
`apply`), but then please indicate some of the intermediate goals, so that we
can follow the chain of reasoning.

Major proof steps, including applications of induction and invocation of the
induction hypothesis, must be stated explicitly. For each case of a proof by
induction, you must list the inductive hypotheses assumed (if any) and the goal
to be proved. Minor proof steps corresponding to `refl`, `simp`, or `linarith`
need not be justified if you think they are obvious (to humans), but you should
say which key lemmas they depend on. You should be explicit whenever you use a
function definition or an introduction rule for an inductive predicate. -/

/-! We prove that for any n, if n is even then n + 1 is odd. We proceed by
induction on the length of the derivation that n is even. If it has length 0,
then the only rule applied is even.zero, and we need to show odd (0 + 1).
But this is just odd 1, which is obtained by applying rule odd.one.
If the last rule applied was even.add_two, then there is some m such that
n = m + 2 and m is even. We want to prove that odd (n + 1), that is, odd (m + 3).
The derivation of even m is one step shorter than that of even n, hence we may
apply the induction hypothesis to get odd (m + 1). Applying rule odd.add_two,
we get odd (m + 3), which is what we wanted. -/

/-! 2.4 (1 point). Prove the same lemma again, but this time in Lean: -/

lemma even_odd {n : ℕ} (heven : even n) :
  odd (n + 1) :=
begin
  induction' heven,
  { simp *,
    exact odd.one, },
  { apply odd.add_two,
    exact ih, }
end

/-! 2.5 (1 point). Prove the following lemma in Lean.

Hint: Recall that `¬ a` is defined as `a → false`. -/

lemma even_not_odd {n : ℕ} (heven : even n) :
  ¬ odd n :=
begin
  intro hodd,
  induction' heven,
  { cases' hodd, },
  { cases' hodd,
    exact ih hodd, }
end

end LoVe
