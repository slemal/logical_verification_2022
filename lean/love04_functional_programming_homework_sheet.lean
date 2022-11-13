import .love04_functional_programming_demo


/-! # LoVe Homework 4: Functional Programming

Homework must be done individually. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/-! ## Question 1 (2 points): Maps

1.1 (1 point). Complete the following definition. The `map_btree` function
should apply its argument `f` to all values of type `α` stored in the tree and
otherwise preserve the tree's structure. -/

def map_btree {α β : Type} (f : α → β) : btree α → btree β
| btree.empty := btree.empty
| (btree.node a l r) := btree.node (f a) (map_btree l) (map_btree r)

/-! 1.2 (1 point). Prove the following lemma about your `map_btree` function. -/

lemma map_btree_iden {α : Type} :
  ∀t : btree α, map_btree (λa, a) t = t :=
begin
  intro t,
  induction' t,
  { refl, },
  { simp [map_btree, ih_t, ih_t_1], },
end


/-! ## Question 2 (4 points): Tail-Recursive Factorials

Recall the definition of the factorial functions: -/

#check fact

/-! 2.1 (2 points). Experienced functional programmers tend to avoid definitions
such as the above, because they lead to a deep call stack. Tail recursion can be
used to avoid this. Results are accumulated in an argument and returned. This
can be optimized by compilers. For factorials, this gives the following
definition: -/

def accufact : ℕ → ℕ → ℕ
| a 0       := a
| a (n + 1) := accufact ((n + 1) * a) n

/-! Prove that, given 1 as the accumulator `a`, `accufact` computes `fact`.

Hint: You will need to prove a generalized version of the statement as a
separate lemma or `have`, because the desired property fixes `a` to 1, which
yields a too weak induction hypothesis. -/

lemma accufact_1_eq_fact (n : ℕ) :
  accufact 1 n = fact n :=
have accufact_a_eq_fact :
  ∀a n, accufact a n = a * fact n :=
  begin
    intros a n,
    induction' n,
    { simp [accufact, fact], },
    { simp [accufact, fact, ih],
      simp [←mul_assoc, mul_comm], },
  end,
show accufact 1 n = fact n, by
  simp [accufact_a_eq_fact 1 n]

/-! 2.2 (2 points). Prove the same property as above again, this time as a
"paper" proof. Follow the guidelines given in question 1.4 of the exercise. -/

/-! We prove a more general result, namely that ∀a n, accufact a n = a * fact n.
The result then follows by taking a = 1.
We prove our generalised result by induction on n. The base case comes down to
proving accufact a 0 = a * fact 0. By definition of accufact, accufact a 0 = a,
and by definition of fact, fact 0 = 1, hence the result is trivial.
For the induction step, we have the induction hypothesis
∀a, accufact a n = a * fact n and we want to prove that
accufact a (n + 1) = a * fact (n + 1). Using the definition of accufact and
fact, this equation becomes accufact (a * (n + 1)) n = a * (n + 1) * fact n.
The result then follows by substituting a * (n + 1) for a in the induction
hypothesis. -/


/-! ## Question 3 (3 points): Gauss's Summation Formula -/

-- `sum_upto f n = f 0 + f 1 + ⋯ + f n`
def sum_upto (f : ℕ → ℕ) : ℕ → ℕ
| 0       := f 0
| (m + 1) := sum_upto m + f (m + 1)

/-! 3.1 (2 point). Prove the following lemma, discovered by Carl Friedrich Gauss
as a pupil.

Hint: The `mul_add` and `add_mul` lemmas might be useful to reason about
multiplication. -/

#check mul_add
#check add_mul

lemma sum_upto_eq :
  ∀m : ℕ, 2 * sum_upto (λi, i) m = m * (m + 1) :=
begin
  intro m,
  induction' m,
  { refl, },
  { simp [sum_upto, ih, mul_add],
    apply eq.symm,
    calc  nat.succ m * nat.succ m + nat.succ m
        = (m + 1) * (m + 1) + (m + 1) :
      by refl
    ... = m * m + m * 1 + 1 * m + 1 * 1 + m + 1 :
      by simp [add_mul, mul_add, add_assoc]
    ... = m * m + m + m + 1 + m + 1 :
      by simp [mul_one]
    ... = m * m + m + 2 * (m + 1) :
      by simp [add_assoc, two_mul]
    ... = m * m + m + (2 * m + 2) :
      by simp [add_assoc, mul_add], },
end

/-! 3.2 (1 point). Prove the following property of `sum_upto`. -/

lemma sum_upto_mul (f g : ℕ → ℕ) :
  ∀n : ℕ, sum_upto (λi, f i + g i) n = sum_upto f n + sum_upto g n :=
begin
  intro n,
  induction' n,
  { refl, },
  { simp [sum_upto, ih],
    simp [add_assoc],
    simp [←add_assoc],
    simp [add_comm], },
end

end LoVe
