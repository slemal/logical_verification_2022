import .love02_backward_proofs_exercise_sheet


/-! # LoVe Homework 3: Forward Proofs

Homework must be done individually. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/-! ## Question 1 (6 points): Connectives and Quantifiers

1.1 (2 points). We have proved or stated three of the six possible implications
between `excluded_middle`, `peirce`, and `double_negation`. Prove the three
missing implications using structured proofs, exploiting the three theorems we
already have. -/

namespace backward_proofs

#check peirce_of_em
#check dn_of_peirce
#check sorry_lemmas.em_of_dn

lemma peirce_of_dn :
  double_negation → peirce :=
assume hdn,
peirce_of_em (sorry_lemmas.em_of_dn hdn)

lemma em_of_peirce :
  peirce → excluded_middle :=
assume hpi,
sorry_lemmas.em_of_dn (dn_of_peirce hpi)


lemma dn_of_em :
  excluded_middle → double_negation :=
assume hem,
dn_of_peirce (peirce_of_em hem)

end backward_proofs

/-! 1.2 (4 points). Supply a structured proof of the commutativity of `∧` under
an `∃` quantifier, using no other lemmas than the introduction and elimination
rules for `∃`, `∧`, and `↔`. -/

lemma exists_and_commute {α : Type} (p q : α → Prop) :
  (∃x, p x ∧ q x) ↔ (∃x, q x ∧ p x) :=
sorry


/-! ## Question 2 (3 points): Fokkink Logic Puzzles

If you have studied Logic and Sets with Prof. Fokkink, you will know he is fond
of logic puzzles. This question is a tribute.

Recall the following tactical proof: -/

lemma weak_peirce :
  ∀a b : Prop, ((((a → b) → a) → a) → b) → b :=
begin
  intros a b habaab,
  apply habaab,
  intro habaa,
  apply habaa,
  intro ha,
  apply habaab,
  intro haba,
  apply ha
end

/-! 2.1 (1 point). Prove the same lemma again, this time by providing a proof
term.

Hint: There is an easy way. -/

lemma weak_peirce₂ :
  ∀a b : Prop, ((((a → b) → a) → a) → b) → b :=
λa b f, f (λg, g (λa, f (λh, a)))

/-! 2.2 (2 points). Prove the same Fokkink lemma again, this time by providing a
structured proof, with `assume`s and `show`s. -/

lemma weak_peirce₃ :
  ∀a b : Prop, ((((a → b) → a) → a) → b) → b :=
fix a b,
assume f : ((((a → b) → a) → a) → b),
have farg : (((a → b) → a) → a) :=
  assume g : ((a → b) → a),
  have garg : (a → b) :=
    assume aa : a,
    have fbrg : (((a → b) → a) → a) :=
      assume h : ((a → b) → a),
      show a, from
        aa,
    show b, from
      f fbrg,
  show a, from
    g garg,
show b, from
  f farg      

end LoVe
