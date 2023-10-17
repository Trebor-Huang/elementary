import Mathlib


inductive Syntax (V : Type) : Type where
| var : V → Syntax V
| const : ℝ → Syntax V
| inv : Syntax V → Syntax V
| root : Syntax V → ℕ → Syntax V
| add : Syntax V → Syntax V → Syntax V
| mul : Syntax V → Syntax V → Syntax V
| sin : Syntax V → Syntax V
| arccos : Syntax V → Syntax V
| exp : Syntax V → Syntax V
| log : Syntax V → Syntax V

namespace Syntax

instance : Coe ℝ (Syntax V) where
  coe := .const

instance : Add (Syntax V) where
  add := .add

instance : Mul (Syntax V) where
  mul := .mul

instance : Neg (Syntax V) where
  neg f := (-1 : ℝ) * f

instance : Inv (Syntax V) where
  inv := .inv

instance : Sub (Syntax V) where
  sub f g := f + (-g)

instance : Div (Syntax V) where
  div f g := f * g⁻¹

noncomputable def eval : Syntax V → (V → ℝ) → ℝ
| .var x, xs => xs x
| .const r, _ => r
| .inv f, xs => (eval f xs)⁻¹
| .root f n, xs => (eval f xs)^(1/(n+1))
| .add f g, xs => eval f xs + eval g xs
| .mul f g, xs => eval f xs * eval g xs
| .sin f, xs => Real.sin (eval f xs)
| .arccos f, xs => Real.arccos (eval f xs)
| .exp f, xs => Real.exp (eval f xs)
| .log f, xs => Real.log (eval f xs)

inductive Domain : Syntax V → (V → ℝ) → Prop where
| var : Domain (.var x) xs
| const : Domain (.const r) xs
| inv : Domain f xs
  → f.eval xs ≠ 0
  → Domain (f ⁻¹) xs
| root : Domain f xs
  → f.eval xs >= 0  -- Cube roots look bad
  → Domain (.root f n) xs
| add : Domain f xs → Domain g xs → Domain (f + g) xs
| mul : Domain f xs → Domain g xs → Domain (f * g) xs
| sin : Domain f xs → Domain (.sin f) xs
| arccos : Domain f xs
  → f.eval xs ∈ Set.Icc (-1) 1
  → Domain (.arccos f) xs
| exp : Domain f xs → Domain (.exp f) xs
| log : Domain f xs
  → f.eval xs > 0
  → Domain (.log f) xs

theorem continuous : Domain f xs → ContinuousAt (f.eval) xs := by
  intro H
  induction f with
  | var => apply continuousAt_apply
  | const => apply continuousAt_const
  | inv f IH =>
    cases H
    apply ContinuousAt.inv₀
    · apply IH; assumption
    · assumption
  | root f n IH =>
    cases H
    apply ContinuousAt.comp (g := (· ^ _))
    · apply Real.continuousAt_rpow_const
      right
      have : (n : ℝ) ≥ 0 := Nat.cast_nonneg n
      simp only [one_div, inv_pos, gt_iff_lt]
      linarith
    · simp_all
  | add =>
    cases H
    apply ContinuousAt.add <;> simp_all
  | mul =>
    cases H
    apply ContinuousAt.mul <;> simp_all
  | sin | arccos | exp =>
    apply ContinuousAt.comp
    · apply Continuous.continuousAt
      continuity
    · cases H; simp_all
  | log =>
    cases H
    apply ContinuousAt.comp
    · apply Real.continuousAt_log
      linarith
    · simp_all

structure IsElementary (f : ℕ → ℝ) where
  formula : Syntax Unit
  domain : ∀ n : ℕ, formula.Domain n
  eq : ∀ n : ℕ, formula.eval n = f n


end Syntax
