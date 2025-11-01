import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Sign

open Finset

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)


/-!
  This file includes Mathlib type lemmas that we were not able to find,
  mostly because they are quite esoteric.
-/


/-! ## Some lemmas about Real.sign. -/

lemma sign_mul_pos {a b : ℝ} (ha : 0 < a) : Real.sign (a * b) = Real.sign b := by
  by_cases hb₀ : 0 < b
  · rw [Real.sign_of_pos hb₀, Real.sign_of_pos (mul_pos ha hb₀)]
  · by_cases hb₁ : b < 0
    · rw [Real.sign_of_neg hb₁, Real.sign_of_neg (mul_neg_of_pos_of_neg ha hb₁)]
    · simp [(by linarith : b = 0)]

lemma sign_pos' {a : ℝ} (h : Real.sign a = 1) : 0 < a := by
  by_contra hnonpos; simp at hnonpos
  by_cases h0 : a = 0
  · rw [Real.sign_eq_zero_iff.mpr h0] at h
    linarith
  · rw [Real.sign_of_neg (lt_of_le_of_ne hnonpos h0 )] at h
    linarith

lemma sign_neg' {a : ℝ} (h : Real.sign a = -1) : a < 0 := by
  by_contra hnonneg; simp at hnonneg
  by_cases h0 : a = 0
  · rw [Real.sign_eq_zero_iff.mpr h0] at h
    linarith
  · rw [Real.sign_of_pos (lt_of_le_of_ne hnonneg ?_)] at h
    linarith
    exact fun a_1 ↦ h0 (id (Eq.symm a_1)) -- very strange

lemma sign_div_pos {a b : ℝ} (hb₀ : b ≠ 0) (hs : Real.sign a = Real.sign b) :
    0 < a / b := by
  rcases Real.sign_apply_eq_of_ne_zero _ hb₀ with (hbs|hbs) <;> rw [hbs] at hs
  · exact div_pos_of_neg_of_neg (sign_neg' hs) (sign_neg' hbs)
  · exact div_pos (sign_pos' hs) (sign_pos' hbs)

lemma real_sign_mul {x y : ℝ} : Real.sign (x * y) = Real.sign x * Real.sign y := by
  obtain (hx | hx | hx) := lt_trichotomy x 0
  · calc
      (x * y).sign  = (-((-x) * y)).sign  := by congr; ring
      _             = - ((-x) * y).sign   := by rw [Real.sign_neg]
      _             = - y.sign            := by congr 1; exact sign_mul_pos (by linarith)
      _             = (-1) * y.sign       := by ring
      _             = x.sign * y.sign     := by congr; exact (Real.sign_of_neg hx).symm
  · rw [hx, zero_mul, Real.sign_zero, zero_mul]
  · rw [sign_mul_pos hx, Real.sign_of_pos hx, one_mul]

lemma real_sign_involution {x : ℝ} : x.sign.sign = x.sign := by
  obtain (hx | hx | hx) := Real.sign_apply_eq x <;> (
  · rw [hx, Real.sign]
    simp
  )

lemma real_sign_div_self {x : ℝ} (hx : x ≠ 0) : 0 <  Real.sign x / x :=
  sign_div_pos hx real_sign_involution

lemma real_sign_mul_self {x : ℝ} (hx : x ≠ 0) : 0 < (Real.sign x) * x := by
  obtain (hx' | hx') := Real.sign_apply_eq_of_ne_zero x hx <;> rw [hx']
  · simp [sign_neg' hx']
  · simp [sign_pos' hx']

lemma real_sign_abs_le {x : ℝ} : |Real.sign x| ≤ 1 := by
  obtain (hx | hx | hx) := Real.sign_apply_eq x <;> simp [hx]


/-! ## Other stuff -/

lemma mul_cancel {a b c : ℝ} (h : a ≠ 0) (h2: a * b = a * c) :
        b = c := by simp_all only [ne_eq, mul_eq_mul_left_iff, or_false]

lemma smul_cancel {a : ℝ} {b c : ℝ²} (h₁ : a ≠ 0) (h₂: a • b = a • c)
    : b = c := by
  refine PiLp.ext ?_
  intro i
  rw [PiLp.ext_iff] at h₂
  have l := h₂ i
  simp [PiLp.smul_apply, smul_eq_mul, mul_eq_mul_left_iff, h₁] at l
  assumption

open Classical in
lemma fin2_im {α : Type} {f : Fin 2 → α}
    : Finset.image f (Finset.univ : Finset (Fin 2)) = {f 0, f 1} := by
  ext
  simp only [mem_image, mem_univ, true_and, Fin.exists_fin_two, Fin.isValue, mem_insert,
    mem_singleton]
  grind

/- This lemma is in mathlib but somehow I cannot get it to work unless it is in this form. -/
lemma forall_in_swap_special {α β : Type} {P : α → β → Prop} {Q : α → Prop} :
    (∀ a, Q a → ∀ b, P a b) ↔ (∀ b, ∀ a, Q a → P a b) :=
  by grind


lemma forall_exists_pos_swap {α : Type} [Fintype α] {P : ℝ → α → Prop}
    (h : ∀ δ a, P δ a → ∀ δ', δ' ≤ δ → P δ' a): (∃ δ > 0, ∀ a, P δ a) ↔ (∀ a, ∃ δ > 0, P δ a) := by
  constructor
  · exact fun ⟨δ,Qδ,Pδ⟩ a ↦ ⟨δ, Qδ, Pδ a⟩
  · intro ha
    by_cases hα : Nonempty α
    · choose fδ hfδ using ha
      have hS : (image fδ univ).Nonempty := by rwa [image_nonempty, univ_nonempty_iff]
      use min' (image fδ univ) hS
      refine ⟨?_,?_⟩
      · rw [gt_iff_lt, Finset.lt_min'_iff]
        intro y hy
        have ⟨x,_,hx⟩ := mem_image.1 hy
        rw [←hx]
        exact (hfδ x).1
      · intro x
        apply h (fδ x) x (hfδ x).2
        exact min'_le _ _ (mem_image_of_mem fδ (mem_univ x))
    · simp_all only [gt_iff_lt, not_nonempty_iff, IsEmpty.forall_iff, and_true, implies_true]
      use 1
      norm_num

def real_interval_δ {x: ℝ} (y : ℝ) (hx : 0 < x) : ∃ δ > 0, ∀ a, |a| ≤ δ → 0 < x + a * y := by
  by_cases hy : y = 0
  · exact ⟨1, by norm_num, fun a _ ↦ by rwa [hy,mul_zero,add_zero]⟩
  · use x / (2 * |y|)
    constructor
    · field_simp [hy]
      simp_all
    · intro a ha
      calc
        0     <   (1/2) * x       := by linarith
        _     =   x + (- (1/2)*x) := by linarith
        _     ≤   x + a * y       := by
          gcongr x + ?_
          field_simp
          rw [←neg_le_neg_iff, ←mul_le_mul_iff_right₀ (a := 2) (by norm_num), neg_neg]
          gcongr 2 * ?_
          apply le_of_max_le_right (?_ : |2 * a * y| ≤ x)
          rw [abs_mul, abs_mul, Nat.abs_ofNat]
          rw [le_div_iff₀ ?_] at ha
          · grind
          · exact mul_pos zero_lt_two (abs_pos.mpr hy)

/-- Pigeonhole lemma of the form that I have not been able to find. -/
lemma finset_infinite_pigeonhole {α β : Type} [Infinite α] {f : α → β} {B : Finset β}
    (hf : ∀ a, f a ∈ B) : ∃ b ∈ B, Set.Infinite (f⁻¹' {b}) := by
  have : Finite B := by exact Finite.of_fintype { x // x ∈ B }
  let f_B := fun (a : α) => (⟨f a, hf a⟩ : B)
  have ⟨b, hb⟩ := Finite.exists_infinite_fiber f_B
  use b
  constructor
  · exact Finset.coe_mem b
  · convert Set.infinite_coe_iff.mp hb
    ext a
    cases b
    simp [f_B]

lemma infinite_distinct_el {α : Type} {S : Set α} (hS : Set.Infinite S) (k : α) : ∃ a ∈ S, a ≠ k := by
  have ⟨a, haS, ha⟩ :=  Set.Infinite.exists_notMem_finset hS ({k} : Finset α)
  exact ⟨a, haS, List.ne_of_not_mem_cons ha⟩

lemma infinite_imp_two_distinct_el  {α : Type} {S : Set α} (hS : S.Infinite) : ∃ a ∈ S, ∃ b ∈ S, a ≠ b := by
  have ⟨a, ha⟩ := Set.Infinite.nonempty hS
  have ⟨b, hb⟩ := infinite_distinct_el hS a
  use a, ha, b, hb.1, hb.2.symm
