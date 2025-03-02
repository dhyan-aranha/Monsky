import Mathlib
import FormalBook.sperner.simplex_basic
import FormalBook.sperner.segment_triangle
import FormalBook.sperner.basic_definitions
import FormalBook.sperner.Rainbow_triangles
import FormalBook.sperner.square


local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "Triangle" => Fin 3 → ℝ²
local notation "Segment" => Fin 2 → ℝ²

open Classical
open BigOperators
open Finset


/- For now we use this formula as the definition of the area.-/
noncomputable def triangle_area (T : Triangle) : ℝ :=
  abs (det T) / 2

/- -/
def is_equal_area_cover (X : Set ℝ²) (S : Set Triangle) : Prop :=
  is_disjoint_cover X S ∧
  (∃ (area : ℝ), ∀ T, (T ∈ S) → triangle_area T = area)



/- This rewriting is for convenience. -/
def disjoint_set {α β : Type} (X : Set α) (f : α → Set β) := ∀ a₁ a₂, a₁ ∈ X → a₂ ∈ X → a₁ ≠ a₂ → Disjoint (f a₁) (f a₂)
def covers {α β} (X : Set α) (Y : Set β) (f : α → Set β) := Y = ⋃ a ∈ X, f a

lemma is_cover_iff (X : Set ℝ²) (S : Set Triangle)
    : is_disjoint_cover X S ↔ covers S X closed_hull ∧ disjoint_set S open_hull := by
  simp [is_cover, is_disjoint_cover, is_disjoint_polygon_set, covers, disjoint_set]
  intro _
  constructor
  · intro h Δ₁ Δ₂ hΔ₁ hΔ₂ hneq
    exact h Δ₁ hΔ₁ Δ₂ hΔ₂ hneq
  · intro h Δ₁ hΔ₁ Δ₂ hΔ₂ hneq
    exact h Δ₁ Δ₂ hΔ₁ hΔ₂ hneq

lemma disjoint_aux {α β : Type} (S₁ S₂ : Set α) (f : α → Set β) (h₁ : disjoint_set S₁ f)
    (h₂ : disjoint_set S₂ f) (h₃ : ∀ a₁ a₂, a₁ ∈ S₁ → a₂ ∈ S₂ → Disjoint (f a₁) (f a₂)) : disjoint_set (S₁ ∪ S₂) f := by
  intro a₁ a₂ ha₁ ha₂ hneq
  cases' ha₁ with ha₁ ha₁ <;> cases' ha₂ with ha₂ ha₂
  · exact h₁ a₁ a₂ ha₁ ha₂ hneq
  · exact h₃ a₁ a₂ ha₁ ha₂
  · exact (h₃ a₂ a₁ ha₂ ha₁ ).symm
  · exact h₂ a₁ a₂ ha₁ ha₂ hneq


/-
  The square can be covered by an even number of triangles.
-/

/- These two triangles dissect the square and have equal area.-/
def Δ₀  : Triangle  := fun | 0 => (v 0 0) | 1 => (v 1 0) | 2 => (v 0 1)
def Δ₀' : Triangle  := fun | 0 => (v 1 0) | 1 => (v 0 1) | 2 => (v 1 1)

lemma areaΔ₀ : triangle_area Δ₀ = 1 / 2 := by
  simp [triangle_area, det, Δ₀]

lemma areaΔ₀' : triangle_area Δ₀' = 1 / 2 := by
  simp [triangle_area, det, Δ₀']


/- Now we show how a cover of size two implies a cover of any even size.-/

/- Elementary stuff about scaling (only in the y direction).-/

def scale_vector (a : ℝ) (y : ℝ²) : ℝ² := fun | 0 => y 0 | 1 => a * y 1

def scale_triangle (a : ℝ) (T : Triangle) : Triangle := fun i ↦ scale_vector a (T i)

lemma scale_triangle_det (a : ℝ) (T : Triangle) :
    det (scale_triangle a T) = a * det T := by
  simp only [det, scale_triangle, scale_vector]
  ring

lemma scale_triangle_area (a : ℝ) (T : Triangle)
    : triangle_area (scale_triangle a T) = |a| * (triangle_area T) := by
  simp only [triangle_area, scale_triangle_det a T, abs_mul, mul_div_assoc]


/- Elementary stuff about translating (only in the y direction).-/

def translate_vector (a : ℝ) (x : ℝ²) : ℝ² := fun | 0 => x 0 | 1 => a + x 1
def translate_triangle (a : ℝ) (T : Triangle) : Triangle := fun i ↦ translate_vector a (T i)

lemma translate_triangle_det (a : ℝ) (T : Triangle) :
    det (translate_triangle a T) = det T := by
  simp only [det, translate_triangle, translate_vector]
  ring

lemma translate_triangle_area (a : ℝ) (T : Triangle)
    : triangle_area (translate_triangle a T) = (triangle_area T) := by
  simp only [triangle_area, translate_triangle_det]

-- Here a different try. Just give a very explicit cover.
noncomputable def zig_part_cover (n : ℕ)
  := Finset.image (fun (s : Fin n) ↦ translate_triangle ((s : ℝ) / (n : ℝ)) (scale_triangle (1 / (n : ℝ)) Δ₀)) univ

noncomputable def zag_part_cover (n : ℕ)
  := Finset.image (fun (s : Fin n) ↦ translate_triangle ((s : ℝ) / (n : ℝ)) (scale_triangle (1 / (n : ℝ)) Δ₀')) univ

lemma zig_cover_size (n : ℕ) : (zig_part_cover n).card = n := by
  unfold zig_part_cover
  by_cases hn : n = 0
  rw [hn]; simp
  rw [Finset.card_image_of_injective]
  · simp only [card_univ, Fintype.card_fin]
  · intro s₁ s₂ hsame
    have hsame := congrArg (fun Δ ↦ Δ 0 1) hsame
    have hn' := (Nat.cast_ne_zero (R := ℝ)).mpr hn
    simp [translate_triangle, translate_vector, div_eq_div_iff hn' hn'] at hsame
    cases' hsame with h h
    · exact Fin.eq_of_val_eq h
    · rw [h] at hn'; simp at hn'

lemma zag_cover_size (n : ℕ) : (zag_part_cover n).card = n := by
  unfold zag_part_cover
  by_cases hn : n = 0
  rw [hn]; simp
  rw [Finset.card_image_of_injective]
  · simp only [card_univ, Fintype.card_fin]
  · intro s₁ s₂ hsame
    have hsame := congrArg (fun Δ ↦ Δ 0 1) hsame
    have hn' := (Nat.cast_ne_zero (R := ℝ)).mpr hn
    simp [translate_triangle, translate_vector, div_eq_div_iff hn' hn'] at hsame
    cases' hsame with h h
    · exact Fin.eq_of_val_eq h
    · rw [h] at hn'; simp at hn'

lemma zig_zag_cover_size (n : ℕ) : (zig_part_cover n ∪ zag_part_cover n).card = 2 * n := by
  have h : (zig_part_cover n ∩ zag_part_cover n).card = 0 := by
    rw [card_eq_zero, ←disjoint_iff_inter_eq_empty, disjoint_left]
    intro _ h₁ h₂
    simp [zig_part_cover, zag_part_cover] at h₁ h₂
    have ⟨s₁,hs₁⟩ := h₁
    have ⟨s₂,hs₂⟩ := h₂
    rw [←hs₂] at hs₁
    have hsame := congrArg (fun Δ ↦ Δ 0 0) hs₁
    simp [translate_triangle, translate_vector, scale_triangle, scale_vector, Δ₀, Δ₀'] at hsame
  simp_rw [card_union, zig_cover_size, zag_cover_size, h, tsub_zero, two_mul]


lemma zig_cover_area {n : ℕ} : ∀ {Δ : Triangle}, Δ ∈ zig_part_cover n → triangle_area Δ = 1 / (2 * n) := by
  intro Δ hΔ
  simp [zig_part_cover] at hΔ
  have ⟨s,hs⟩ := hΔ
  rw [←hs, translate_triangle_area, scale_triangle_area, areaΔ₀]
  simp

lemma zag_cover_area {n : ℕ} : ∀ {Δ : Triangle}, Δ ∈ zag_part_cover n → triangle_area Δ = 1 / (2 * n) := by
  intro Δ hΔ
  simp [zag_part_cover] at hΔ
  have ⟨s,hs⟩ := hΔ
  rw [←hs, translate_triangle_area, scale_triangle_area, areaΔ₀']
  simp

lemma fin_el_bound {n : ℕ} {x: ℝ} {s₁ s₂ : Fin n} (h₁l : x - 1 < s₁) (h₁u : s₁ < x)
    (h₂l : x - 1 < s₂)  (h₂u : s₂ < x) : s₁ = s₂ := by
  wlog hl : s₁ ≤ s₂
  · refine (this h₂l h₂u h₁l h₁u (le_of_not_ge hl)).symm
  · refine Fin.le_antisymm_iff.mpr ⟨hl, ?_⟩
    by_contra hc
    rw [not_le, @Fin.lt_iff_val_lt_val, @Nat.lt_iff_add_one_le,
        ←Nat.cast_le (α := ℝ), @Nat.cast_add, @Nat.cast_one] at hc
    linarith

lemma zig_open_disjoint{n : ℕ} : disjoint_set ((zig_part_cover n) : Set Triangle) open_hull := by
  by_cases nsign : ↑n > 0
  · intro Δ₁ Δ₂ hΔ₁ hΔ₂ hΔneq
    simp [mem_coe, zig_part_cover] at hΔ₁ hΔ₂
    have ⟨s₁,hs₁⟩ := hΔ₁
    have ⟨s₂,hs₂⟩ := hΔ₂
    rw [@Set.disjoint_right]
    intro x hx₂ hx₁
    rw [←hs₁, open_triangle_iff] at hx₁
    rw [←hs₂, open_triangle_iff] at hx₂
    have hx₁₀ := hx₁ 0
    have hx₁₁ := hx₁ 1
    have hx₁₂ := hx₁ 2
    have hx₂₀ := hx₂ 0
    have hx₂₂ := hx₂ 2
    · refine hΔneq ?_
      simp [Tco, sign_seg, set, det, scale_triangle, translate_triangle, scale_triangle, translate_vector, Tside, scale_vector, Δ₀] at hx₁₀ hx₁₁ hx₁₂ hx₂₀ hx₂₂
      field_simp [nsign] at hx₁₀ hx₁₁ hx₁₂ hx₂₀ hx₂₂
      rw [←hs₁, ←hs₂, fin_el_bound (by linarith) hx₁₂ (by linarith) hx₂₂]
    · simp [det, translate_triangle, scale_triangle, Δ₀, translate_vector, scale_vector, Nat.not_eq_zero_of_lt nsign]
    · simp [det, translate_triangle, scale_triangle, Δ₀, translate_vector, scale_vector, Nat.not_eq_zero_of_lt nsign]
  · simp [Nat.eq_zero_of_not_pos nsign, zig_part_cover, disjoint_set]

lemma zag_open_disjoint{n : ℕ} : disjoint_set ((zag_part_cover n) : Set Triangle) open_hull := by
  by_cases nsign : ↑n > 0
  · intro Δ₁ Δ₂ hΔ₁ hΔ₂ hΔneq
    simp [mem_coe, zag_part_cover] at hΔ₁ hΔ₂
    have ⟨s₁,hs₁⟩ := hΔ₁
    have ⟨s₂,hs₂⟩ := hΔ₂
    rw [@Set.disjoint_right]
    intro x hx₂ hx₁
    rw [←hs₁, open_triangle_iff] at hx₁
    rw [←hs₂, open_triangle_iff] at hx₂
    have hx₁₀ := hx₁ 0
    have hx₁₁ := hx₁ 1
    have hx₁₂ := hx₁ 2
    have hx₂₀ := hx₂ 0
    have hx₂₂ := hx₂ 2
    · refine hΔneq ?_
      simp [Tco, sign_seg, set, det, scale_triangle, translate_triangle, scale_triangle, translate_vector, Tside, scale_vector, Δ₀'] at hx₁₀ hx₁₁ hx₁₂ hx₂₀ hx₂₂
      ring_nf at hx₁₀ hx₁₁ hx₁₂ hx₂₀ hx₂₂
      field_simp [nsign] at hx₁₀ hx₁₁ hx₁₂ hx₂₀ hx₂₂
      rw [←hs₁, ←hs₂, fin_el_bound (x := x 1 * ↑n) (s₁ := s₁) (s₂ := s₂) (by linarith) (by linarith) (by linarith) (by linarith)]
    · simp [det, translate_triangle, scale_triangle, Δ₀', translate_vector, scale_vector, Nat.not_eq_zero_of_lt nsign]
      field_simp [Nat.not_eq_zero_of_lt nsign]
      ring_nf; norm_num
    · simp [det, translate_triangle, scale_triangle, Δ₀', translate_vector, scale_vector, Nat.not_eq_zero_of_lt nsign]
      field_simp [Nat.not_eq_zero_of_lt nsign]
      ring_nf; norm_num
  · simp [Nat.eq_zero_of_not_pos nsign, zag_part_cover, disjoint_set]

lemma zig_zag_open_disjoint {n : ℕ}
    : ∀ a₁ a₂, a₁ ∈ (zig_part_cover n) → a₂ ∈ (zag_part_cover n) → Disjoint (open_hull a₁) (open_hull a₂) := by
  by_cases nsign : ↑n > 0
  · intro Δ₁ Δ₂ hΔ₁ hΔ₂
    simp [mem_coe, zig_part_cover, zag_part_cover] at hΔ₁ hΔ₂
    have ⟨s₁,hs₁⟩ := hΔ₁
    have ⟨s₂,hs₂⟩ := hΔ₂
    rw [@Set.disjoint_right]
    intro x hx₂ hx₁
    rw [←hs₁, open_triangle_iff] at hx₁
    rw [←hs₂, open_triangle_iff] at hx₂
    have hx₁₀ := hx₁ 0
    have hx₁₁ := hx₁ 1
    have hx₁₂ := hx₁ 2
    have hx₂₀ := hx₂ 0
    have hx₂₁ := hx₂ 1
    have hx₂₂ := hx₂ 2
    · simp [Tco, sign_seg, set, det, scale_triangle, translate_triangle, scale_triangle, translate_vector, Tside, scale_vector, Δ₀, Δ₀'] at hx₁₀ hx₁₁ hx₁₂ hx₂₀ hx₂₁ hx₂₂
      ring_nf at hx₁₀ hx₁₁ hx₁₂ hx₂₀ hx₂₁ hx₂₂
      field_simp [nsign] at hx₁₀ hx₁₁ hx₁₂ hx₂₀ hx₂₁ hx₂₂
      have l := fin_el_bound (x := x 1 * ↑n) (s₁ := s₁) (s₂ := s₂) (by linarith) (by linarith) (by linarith) (by linarith)
      rw [l] at hx₁₀ hx₁₂
      linarith
    · simp [det, translate_triangle, scale_triangle, Δ₀', translate_vector, scale_vector, Nat.not_eq_zero_of_lt nsign]
      field_simp [Nat.not_eq_zero_of_lt nsign]
      ring_nf; norm_num
    · simp [det, translate_triangle, scale_triangle, Δ₀, translate_vector, scale_vector, Nat.not_eq_zero_of_lt nsign]
  · simp [Nat.eq_zero_of_not_pos nsign, zag_part_cover, disjoint_set]


lemma zig_zag_covers_square {n : ℕ} (hn : n ≠ 0)
    : covers ((zig_part_cover n ∪ zag_part_cover n) : Set Triangle) (closed_hull unit_square) closed_hull := by
  ext x
  simp [closed_unit_square_eq]
  constructor
  · intro hx
    -- Determine in which part of the cover x falls.
    -- Nat.floor (n * x 1) is not right unfortunately when x 1 = 1
    by_cases hx₁ : x 1 < 1
    · let j := Nat.floor (n * x 1)
      by_cases hj : (n * x 1 - j) + x 0 ≤ 1
      · use translate_triangle ((j : ℝ) / (n : ℝ)) (scale_triangle (1 / (n : ℝ)) Δ₀)
        constructor
        · left
          rw [zig_part_cover,mem_image]
          refine ⟨⟨j,?_⟩ ,by simp⟩
          rw [propext (Nat.floor_lt' hn)]
          convert (mul_lt_mul_left ?_).mpr hx₁
          · ring
          · rw [Nat.cast_pos]
            exact Nat.zero_lt_of_ne_zero hn
        · rw [closed_triangle_iff]
          · intro i
            fin_cases i <;> (
              simp [Tco, sign_seg, set, det, scale_triangle, translate_triangle, scale_triangle, translate_vector, Tside, scale_vector, Δ₀, Δ₀'];
              field_simp [hn]
              ring_nf
              try linarith [hx 0 ]
            )
            convert Nat.floor_le (a := ↑n * x 1) ?_ using 1
            · exact mul_comm _ _
            · exact Left.mul_nonneg (Nat.cast_nonneg' _) (hx 1).1
          · rw [translate_triangle_det, scale_triangle_det, mul_ne_zero_iff_right]
            · simp only [one_div, ne_eq, inv_eq_zero, Nat.cast_eq_zero, hn, not_false_eq_true]
            · simp [det, Δ₀]
      · use translate_triangle ((j : ℝ) / (n : ℝ)) (scale_triangle (1 / (n : ℝ)) Δ₀')
        constructor
        · right
          rw [zag_part_cover,mem_image]
          refine ⟨⟨j,?_⟩ ,by simp⟩
          rw [propext (Nat.floor_lt' hn)]
          convert (mul_lt_mul_left ?_).mpr hx₁
          · ring
          · rw [Nat.cast_pos]
            exact Nat.zero_lt_of_ne_zero hn
        · rw [closed_triangle_iff]
          · intro i
            fin_cases i <;> (
              simp [Tco, sign_seg, set, det, scale_triangle, translate_triangle, scale_triangle, translate_vector, Tside, scale_vector, Δ₀, Δ₀'];
              field_simp [hn]
              ring_nf
              try linarith [hx 0 ]
            )
            convert sub_nonneg.2 (le_of_lt (Nat.lt_floor_add_one (↑n * x 1))) using 1
            ring
          · rw [translate_triangle_det, scale_triangle_det, mul_ne_zero_iff_right]
            · simp only [one_div, ne_eq, inv_eq_zero, Nat.cast_eq_zero, hn, not_false_eq_true]
            · simp [det, Δ₀']
    · have hx₁ : x 1 = 1 := by linarith [hx 1]
      · use translate_triangle (( n  - 1 ) / (n : ℝ)) (scale_triangle (1 / (n : ℝ)) Δ₀')
        constructor
        · right
          rw [zag_part_cover,mem_image]
          refine ⟨⟨n - 1, Nat.sub_one_lt hn⟩,?_⟩
          simp only [mem_univ, one_div, true_and]
          conv => arg 1; arg 1; arg 1; rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn), Nat.cast_one]
        · rw [closed_triangle_iff]
          · intro i
            fin_cases i <;> (
              simp [Tco, sign_seg, set, det, scale_triangle, translate_triangle, scale_triangle, translate_vector, Tside, scale_vector, Δ₀, Δ₀', hx₁];
              field_simp [hn]
              ring_nf
              try linarith [hx 0]
            )
            rw [mul_assoc, mul_inv_cancel₀ ( Nat.cast_ne_zero.mpr hn)]
            linarith [hx 0]
          · rw [translate_triangle_det, scale_triangle_det, mul_ne_zero_iff_right]
            · simp only [one_div, ne_eq, inv_eq_zero, Nat.cast_eq_zero, hn, not_false_eq_true]
            · simp [det, Δ₀']
  · rintro ⟨S,(hzig | hzag),hS⟩
    · simp [zig_part_cover] at hzig
      have ⟨s, hs⟩ := hzig
      rw [←hs, closed_triangle_iff] at hS
      · have hs₀ := hS 0
        have hs₁ := hS 1
        have hs₂ := hS 2
        simp [Tco, sign_seg, set, det, scale_triangle, translate_triangle, scale_triangle, translate_vector, Tside, scale_vector, Δ₀, Δ₀'] at hs₀ hs₁ hs₂
        field_simp [hn] at hs₀ hs₁ hs₂
        intro i; constructor <;> (fin_cases i <;> simp; linarith)
        · convert div_le_div_of_nonneg_right (le_trans (Nat.cast_nonneg' _) hs₂) (Nat.cast_nonneg' n)
          · simp only [zero_div]
          · refine Eq.symm (mul_div_cancel_right₀ (x 1) (Nat.cast_ne_zero.mpr hn))
        · rw [add_assoc, le_neg_add_iff_le] at hs₀
          have this := le_trans hs₁ hs₀
          rw [le_neg_add_iff_le] at this
          -- Following part is repeated below
          have this2 := div_le_div_of_nonneg_right this (Nat.cast_nonneg' n)
          rw [(mul_div_cancel_right₀ (x 1) (Nat.cast_ne_zero.mpr hn))] at this2
          apply le_trans this2
          apply (div_le_one₀ (Nat.cast_pos'.mpr (Nat.zero_lt_of_ne_zero hn))).mpr
          convert (Nat.cast_le (α := ℝ)).2 (@Nat.lt_iff_add_one_le.1 s.prop)
          simp only [Nat.cast_add, Nat.cast_one]
      · rw [translate_triangle_det, scale_triangle_det, mul_ne_zero_iff_right]
        · exact inv_ne_zero (Nat.cast_ne_zero.mpr hn)
        · simp [det, Δ₀]
    · simp [zag_part_cover] at hzag
      have ⟨s, hs⟩ := hzag
      rw [←hs, closed_triangle_iff] at hS
      · have hs₀ := hS 0
        have hs₁ := hS 1
        have hs₂ := hS 2
        simp [Tco, sign_seg, set, det, scale_triangle, translate_triangle, scale_triangle, translate_vector, Tside, scale_vector, Δ₀, Δ₀'] at hs₀ hs₁ hs₂
        field_simp [hn] at hs₀ hs₁ hs₂
        conv at hs₀ => ring_nf
        conv at hs₁ => ring_nf
        conv at hs₂ => ring_nf
        intro i; constructor <;> (fin_cases i <;> simp; linarith)
        · have step₁ : 0 ≤ (x 1 * ↑n - ↑↑s) := le_trans hs₁ (by linarith)
          have step₂ : 0 ≤ x 1 * ↑n := le_trans (b := (s : ℝ)) (Nat.cast_nonneg' _) (by linarith)
          convert div_le_div_of_nonneg_right (c := (n : ℝ)) step₂ ?_
          · simp only [zero_div]
          · refine Eq.symm (mul_div_cancel_right₀ (x 1) (Nat.cast_ne_zero.mpr hn))
          · exact Nat.cast_nonneg' n
        · have step₁ : x 1 * ↑n ≤ ↑↑s + 1 := by linarith
          have step₂ := div_le_div_of_nonneg_right step₁ (Nat.cast_nonneg' n)
          -- This part is the same as above and probably not efficient
          rw [(mul_div_cancel_right₀ (x 1) (Nat.cast_ne_zero.mpr hn))] at step₂
          apply le_trans step₂
          apply (div_le_one₀ (Nat.cast_pos'.mpr (Nat.zero_lt_of_ne_zero hn))).mpr
          convert (Nat.cast_le (α := ℝ)).2 (@Nat.lt_iff_add_one_le.1 s.prop)
          simp only [Nat.cast_add, Nat.cast_one]
      · rw [translate_triangle_det, scale_triangle_det, mul_ne_zero_iff_right]
        · exact inv_ne_zero (Nat.cast_ne_zero.mpr hn)
        · simp [det, Δ₀']


theorem monsky_easy_direction' {n : ℕ} (hn : Even n) (hnneq : n ≠ 0)
    : (∃ (S : Finset Triangle), is_equal_area_cover (closed_hull unit_square) S ∧ S.card = n) := by
  have ⟨m,hm⟩ := hn
  use (zig_part_cover m ∪ zag_part_cover m)
  refine ⟨⟨?_,?_⟩,?_⟩
  · rw [is_cover_iff]
    refine ⟨?_,?_⟩
    · convert zig_zag_covers_square (n := m) ?_
      · simp only [coe_union]
      · intro h; apply hnneq
        rw [hm,h,add_zero]
    · convert disjoint_aux (S₁ := zig_part_cover m) (S₂ := (zag_part_cover m : Set Triangle)) (f := open_hull) zig_open_disjoint zag_open_disjoint zig_zag_open_disjoint
      exact coe_union (zig_part_cover m) (zag_part_cover m)
  · use 1 / (2*m)
    intro Δ hΔ
    simp at hΔ
    cases' hΔ with hΔ hΔ
    · exact zig_cover_area hΔ
    · exact zag_cover_area hΔ
  · convert zig_zag_cover_size m
    linarith
