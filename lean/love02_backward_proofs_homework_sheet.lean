import .love02_backward_proofs_exercise_sheet


/-! # LoVe Homework 2: Backward Proofs

Homework must be done individually. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe

namespace backward_proofs


/-! ## Question 1 (4 points): Connectives and Quantifiers

1.1 (3 points). Complete the following proofs using basic tactics such as
`intro`, `apply`, and `exact`.

Hint: Some strategies for carrying out such proofs are described at the end of
Section 2.3 in the Hitchhiker's Guide. -/

lemma B (a b c : Prop) :
  (a → b) → (c → a) → c → b :=
begin
  intros hab hca c,
  apply hab,
  exact hca c,
end

lemma S (a b c : Prop) :
  (a → b → c) → (a → b) → a → c :=
begin
  intros habc hab ha,
  apply habc,
  exact ha,
  exact hab ha,
end

lemma more_nonsense (a b c : Prop) :
  (c → (a → b) → a) → c → b → a :=
begin
  intros hcaba hc hb,
  apply hcaba,
  exact hc,
  intro ha,
  exact hb,
end

lemma even_more_nonsense (a b c : Prop) :
  (a → a → b) → (b → c) → a → b → c :=
begin
  intros haab hbc ha hb,
  exact hbc hb,
end

/-! 1.2 (1 point). Prove the following lemma using basic tactics. -/

lemma weak_peirce (a b : Prop) :
  ((((a → b) → a) → a) → b) → b :=
begin
  intro f,
  apply f,
  intro g,
  apply g,
  intro a,
  apply f,
  intro h,
  exact a,
end


/-! ## Question 2 (5 points): Logical Connectives

2.1 (1 point). Prove the following property about implication using basic
tactics.

Hints:

* Keep in mind that `¬ a` is the same as `a → false`. You can start by invoking
  `rw not_def` if this helps you.

* You will need to apply the elimination rules for `∨` and `false` at some
  point. -/

lemma about_implication (a b : Prop) :
  ¬ a ∨ b → a → b :=
begin
  intros hab ha,
  apply or.elim hab,
  { intro hna,
    apply false.elim,
    exact hna ha, },
  { intro hb,
  exact hb, },
end

/-! 2.2 (2 points). Prove the missing link in our chain of classical axiom
implications.

Hints:

* You can use `rw double_negation` to unfold the definition of
  `double_negation`, and similarly for the other definitions.

* You will need to apply the double negation hypothesis for `a ∨ ¬ a`. You will
  also need the left and right introduction rules for `∨` at some point. -/

#check excluded_middle
#check peirce
#check double_negation

lemma em_of_dn :
  double_negation → excluded_middle :=
begin
  rw double_negation,
  rw excluded_middle,
  intros hdn a,
  apply hdn,
  intro hnem,
  apply hnem,
  apply or.intro_right,
  intro ha,
  apply hnem,
  apply or.intro_left,
  exact ha,
end

/-! 2.3 (2 points). We have proved three of the six possible implications
between `excluded_middle`, `peirce`, and `double_negation`. State and prove the
three missing implications, exploiting the three theorems we already have. -/

#check peirce_of_em
#check dn_of_peirce
#check em_of_dn

lemma em_of_pierce :
  peirce → excluded_middle :=
begin
  intro hp,
  apply em_of_dn,
  exact dn_of_peirce hp,
end

lemma dn_of_em :
  excluded_middle → double_negation :=
begin
  intro hem,
  apply dn_of_peirce,
  exact peirce_of_em hem,
end

lemma peirce_of_dn :
  double_negation → peirce :=
begin
  intro hdn,
  apply peirce_of_em,
  exact em_of_dn hdn,
end

end backward_proofs

end LoVe
