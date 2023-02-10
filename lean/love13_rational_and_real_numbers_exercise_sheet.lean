import .love05_inductive_predicates_demo
import .love13_rational_and_real_numbers_demo


/-! # LoVe Exercise 13: Rational and Real Numbers -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/-! ## Question 1: Rationals

1.1. Prove the following lemma.

Hint: The lemma `fraction.mk.inj_eq` might be useful. -/

#check fraction.mk.inj_eq

lemma fraction.ext (a b : fraction) (hnum : fraction.num a = fraction.num b)
    (hdenom : fraction.denom a = fraction.denom b) :
  a = b :=
begin
  cases' a, cases' b,
  rw fraction.mk.inj_eq,
  simp at *,
  apply and.intro; assumption,
end

/-! 1.2. Extending the `fraction.has_mul` instance from the lecture, declare
`fraction` as an instance of `semigroup`.

Hint: Use the lemma `fraction.ext` above, and possibly `fraction.mul_num`, and
`fraction.mul_denom`. -/

#check fraction.ext
#check fraction.mul_num
#check fraction.mul_denom

@[instance] def fraction.semigroup : semigroup fraction :=
{ mul_assoc := by intros a b c; apply fraction.ext; simp [mul_assoc],
  ..fraction.has_mul }

/-! 1.3. Extending the `rat.has_mul` instance from the lecture, declare `rat` as
an instance of `semigroup`. -/

@[instance] def rat.semigroup : semigroup rat :=
{ mul_assoc :=
    begin
      intros a b c,
      apply quotient.induction_on a,
      apply quotient.induction_on b,
      apply quotient.induction_on c,
      intros a b c,
      apply quotient.sound,
      simp [mul_assoc],
    end,
  ..rat.has_mul }

end LoVe
