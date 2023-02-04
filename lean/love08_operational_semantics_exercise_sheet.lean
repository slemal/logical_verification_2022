import .love08_operational_semantics_demo


/-! # LoVe Exercise 8: Operational Semantics -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/-! ## Question 1: Guarded Command Language

In 1976, E. W. Dijkstra introduced the guarded command language (GCL), a
minimalistic imperative language with built-in nondeterminism. A grammar for one
of its variants is given below:

    S  ::=  x := e       -- assignment
         |  assert b     -- assertion
         |  S ; S        -- sequential composition
         |  S | ⋯ | S    -- nondeterministic choice
         |  loop S       -- nondeterministic iteration

Assignment and sequential composition are as in the WHILE language. The other
statements have the following semantics:

* `assert b` aborts if `b` evaluates to false; otherwise, the command is a
  no-op.

* `S | ⋯ | S` chooses any of the branches and executes it, ignoring the other
  branches.

* `loop S` executes `S` any number of times.

In Lean, GCL is captured by the following inductive type: -/

namespace gcl

inductive stmt (σ : Type) : Type
| assign : string → (σ → ℕ) → stmt
| assert : (σ → Prop) → stmt
| seq    : stmt → stmt → stmt
| choice : list stmt → stmt
| loop   : stmt → stmt

infixr ` ;; ` : 90 := stmt.seq

/-! The parameter `σ` abstracts over the state type. It is necessary as a work
around for a Lean bug. Below we will take `σ := state`.

1.1. Complete the following big-step semantics, based on the informal
specification of GCL above. -/

inductive big_step : (stmt state × state) → state → Prop
| assign {x a s} :
  big_step (stmt.assign x a, s) (s{x ↦ a s})
| assert {b : state → Prop} {s} (hcond : b s) :
  big_step (stmt.assert b, s) s
| seq {S T s t u}
    (hS : big_step (S, s) t)
    (hT : big_step (T, t) u) :
  big_step (S ;; T, s) u
| choice {Ss s t} (i) (hless : i < list.length Ss)
    (hbody : big_step (list.nth_le Ss i hless, s) t) :
  big_step (stmt.choice Ss, s) t
| no_loop {S s} :
  big_step (stmt.loop S, s) s
| loop {S s t u}
    (hbody: big_step (S, s) t)
    (hrest : big_step (stmt.loop S, t) u) :
  big_step (stmt.loop S, s) u

infix ` ⟹ ` : 110 := big_step

/-! 1.2. Prove the following inversion rules, as we did in the lecture for the
WHILE language. -/

@[simp] lemma big_step_assign_iff {x a s t} :
  (stmt.assign x a, s) ⟹ t ↔ t = s{x ↦ a s} :=
begin
  apply iff.intro; intro h,
  { cases' h,
    refl, },
  { rw h,
    exact big_step.assign, }
end

@[simp] lemma big_step_assert {b s t} :
  (stmt.assert b, s) ⟹ t ↔ t = s ∧ b s :=
begin
  apply iff.intro; intro h,
  { cases' h,
    apply and.intro,
    { refl, },
    { exact hcond, } },
  { cases' h,
    rw left,
    exact big_step.assert right, }
end

@[simp] lemma big_step_seq_iff {S₁ S₂ s t} :
  (stmt.seq S₁ S₂, s) ⟹ t ↔ (∃u, (S₁, s) ⟹ u ∧ (S₂, u) ⟹ t) :=
begin
  apply iff.intro; intro h,
  { cases' h,
    apply exists.intro,
    apply and.intro; assumption, },
  { cases' h,
    cases' h,
    apply big_step.seq,
    { exact left, },
    { exact right, } }
end

lemma big_step_loop {S s u} :
  (stmt.loop S, s) ⟹ u ↔
  (s = u ∨ (∃t, (S, s) ⟹ t ∧ (stmt.loop S, t) ⟹ u)) :=
begin
  apply iff.intro; intro h,
  { cases' h,
    { apply or.inl; refl, },
    { apply or.inr,
      apply exists.intro,
      apply and.intro; assumption, } },
  { cases' h,
    { rw h; exact big_step.no_loop, },
    { cases' h with t,
      cases' h,
      apply big_step.loop; assumption, } }
end

@[simp] lemma big_step_choice {Ss s t} :
  (stmt.choice Ss, s) ⟹ t ↔
  (∃(i : ℕ) (hless : i < list.length Ss),
     (list.nth_le Ss i hless, s) ⟹ t) :=
begin
  apply iff.intro; intro h,
  { cases' h,
    apply exists.intro i,
    apply exists.intro hless,
    exact h, },
  { cases' h with i,
    cases' h with hless,
    apply big_step.choice; assumption, }
end

end gcl

/-! 1.3. Complete the translation below of a deterministic program to a GCL
program, by filling in the `sorry` placeholders below. -/

def gcl_of : stmt → gcl.stmt state
| stmt.skip         := gcl.stmt.assert (λ_, true)
| (stmt.assign x a) := gcl.stmt.assign x a
| (S ;; T)          := (gcl_of S ;; gcl_of T)
| (stmt.ite b S T)  :=
  gcl.stmt.choice [
    gcl.assert b ;; gcl_of S,
    gcl.assert (λs, ¬ b s) ;; gcl_of T]
| (stmt.while b S)  :=
  gcl.stmt.loop (
    gcl.assert b ;;
    gcl_of S) ;;
  gcl.stmt.assert (λs, ¬ b s)

/-! 1.4. In the definition of `gcl_of` above, `skip` is translated to
`assert (λ_, true)`. Looking at the big-step semantics of both constructs, we
can convince ourselves that it makes sense. Can you think of other correct ways
to define the `skip` case? -/

/-

* `loop (assert _)`

-/


/-! ## Question 2: Program Equivalence

For this question, we introduce the notion of program equivalence: `S₁ ≈ S₂`. -/

def big_step_equiv (S₁ S₂ : stmt) : Prop :=
∀s t, (S₁, s) ⟹ t ↔ (S₂, s) ⟹ t

infix ` ≈ ` := big_step_equiv

/-! Program equivalence is a equivalence relation, i.e., it is reflexive,
symmetric, and transitive. -/

@[refl] lemma big_step_equiv.refl {S : stmt} :
  S ≈ S :=
fix s t,
show (S, s) ⟹ t ↔ (S, s) ⟹ t, from
  by refl

@[symm] lemma big_step_equiv.symm {S₁ S₂ : stmt}:
  S₁ ≈ S₂ → S₂ ≈ S₁ :=
assume h : S₁ ≈ S₂,
fix s t,
show (S₂, s) ⟹ t ↔ (S₁, s) ⟹ t, from
  iff.symm (h s t)

@[trans] lemma big_step_equiv.trans {S₁ S₂ S₃ : stmt} (h₁₂ : S₁ ≈ S₂)
    (h₂₃ : S₂ ≈ S₃) :
  S₁ ≈ S₃ :=
fix s t,
show (S₁, s) ⟹ t ↔ (S₃, s) ⟹ t, from
  iff.trans (h₁₂ s t) (h₂₃ s t)

/-! 2.1. Prove the following program equivalences. -/

lemma big_step_equiv.skip_assign_id {x} :
  stmt.assign x (λs, s x) ≈ stmt.skip :=
begin
  intros s t; apply iff.intro; intro h,
  { cases' h,
    simp, },
  { cases' h,
    simp, }
end

lemma big_step_equiv.seq_skip_left {S : stmt} :
  stmt.skip ;; S ≈ S :=
begin
  intros s t; apply iff.intro; intro h,
  { cases' h,
    cases' h_1,
    exact h, },
  { apply big_step.seq,
    { exact big_step.skip, },
    { exact h, } }
end

lemma big_step_equiv.seq_skip_right {S : stmt} :
  S ;; stmt.skip ≈ S :=
begin
  intros s t; apply iff.intro; intro h,
  { cases' h,
    cases' h_1,
    exact h, },
  { apply big_step.seq,
    { exact h, },
    { exact big_step.skip, } }
end

lemma big_step_equiv.ite_seq_while {b} {S : stmt} :
  stmt.ite b (S ;; stmt.while b S) stmt.skip ≈ stmt.while b S :=
begin
  intros s t; apply iff.intro; intro h,
  { cases' h; cases' h,
    { apply big_step.while_true; assumption, },
    { apply big_step.while_false; assumption, } },
  { cases' h,
    { apply big_step.ite_true,
      { exact hcond, },
      { apply big_step.seq; assumption, } },
    { apply big_step.ite_false,
      { exact hcond, },
      { exact big_step.skip, } } }
end

/-! 2.2 (**optional**). Program equivalence can be used to replace subprograms
by other subprograms with the same semantics. Prove the following so-called
congruence rules: -/

lemma big_step_equiv.seq_congr {S₁ S₂ T₁ T₂ : stmt} (hS : S₁ ≈ S₂)
    (hT : T₁ ≈ T₂) :
  S₁ ;; T₁ ≈ S₂ ;; T₂ :=
begin
  intros s t; apply iff.intro; intro h,
  { cases' h,
    apply big_step.seq,
    { rw ←hS; assumption, },
    { rw ←hT; assumption, } },
  { cases' h,
    apply big_step.seq,
    { rw hS; assumption, },
    { rw hT; assumption, } }
end

lemma big_step_equiv.ite_congr {b} {S₁ S₂ T₁ T₂ : stmt} (hS : S₁ ≈ S₂)
    (hT : T₁ ≈ T₂) :
  stmt.ite b S₁ T₁ ≈ stmt.ite b S₂ T₂ :=
begin
  intros s t; apply iff.intro; intro h,
  { cases' h,
    { apply big_step.ite_true,
      { exact hcond, },
      { rw ←hS; assumption, } },
    { apply big_step.ite_false,
      { exact hcond, },
      { rw ←hT; assumption, } } },
  { cases' h,
    { apply big_step.ite_true,
      { exact hcond, },
      { rw hS; assumption, } },
    { apply big_step.ite_false,
      { exact hcond, },
      { rw hT; assumption, } } }
end

lemma denote_equiv.while_congr {b} {S₁ S₂ : stmt} (hS : S₁ ≈ S₂) :
  stmt.while b S₁ ≈ stmt.while b S₂ :=
begin
  intros s t; apply iff.intro; intro h,
  { induction' h,
    { apply big_step.while_true,
      { exact hcond, },
      { rw ←hS; assumption, },
      { apply ih_h_1; assumption, } },
    { apply big_step.while_false; assumption, } },
  { induction' h,
    { apply big_step.while_true,
      { exact hcond, },
      { rw hS; assumption, },
      { apply ih_h_1; assumption, } },
    { apply big_step.while_false; assumption, } }
end

end LoVe
