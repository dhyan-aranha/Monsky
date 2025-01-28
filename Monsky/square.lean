import Mathlib
import Mathlib.Tactic
import Monsky.simplex_basic
import Monsky.segment_triangle
import Monsky.miscellaneous
import Monsky.basic_definitions


local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "Triangle" => Fin 3 → ℝ²
local notation "Segment" => Fin 2 → ℝ²

open Classical
open BigOperators
open Finset


/-
  Basic properties about the unit square, i.e. the square with vertices 00, 10, 11, 01.
-/

def unit_square : Fin 4 → ℝ² := (fun | 0 => v 0 0 | 1 => v 1 0 | 2 => v 1 1 | 3 => v 0 1)

lemma closed_unit_square_eq : closed_hull unit_square = {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1} := by
  ext x
  constructor
  · intro ⟨α, hα, hxα⟩
    intro i
    rw [←hxα]
    constructor
    · fin_cases i <;> simp [unit_square, Fin.sum_univ_four, Left.add_nonneg, v, hα.1]
    · rw [←hα.2]
      fin_cases i <;>
      ( simp [unit_square, Fin.sum_univ_four, v]
        linarith [hα.1 0, hα.1 1, hα.1 2, hα.1 3])
  · intro hx
    use fun
          | 0 => (1 + min (x 0) (x 1) - (x 0) - (x 1))
          | 1 => x 0 - min (x 0) (x 1)
          | 2 => min (x 0) (x 1)
          | 3 => x 1 - min (x 0) (x 1)
    refine ⟨⟨?_,?_⟩,?_⟩
    · intro i
      fin_cases i <;> simp [hx 0, hx 1]
      cases min_choice (x 0) (x 1) <;> simp_all
      linarith [hx 0]
    · rw [Fin.sum_univ_four]
      ring
    · apply PiLp.ext
      intro i
      fin_cases i <;> simp [Fin.sum_univ_four, unit_square, v]


-- The open unit square is more or less the same
lemma open_unit_square_eq : open_hull unit_square = {x | ∀ i, 0 < x i ∧ x i < 1} := by
  ext x
  constructor
  · intro ⟨α, hα, hxα⟩
    intro i
    rw [←hxα]
    constructor
    · fin_cases i <;> simp [unit_square, Fin.sum_univ_four, Left.add_pos,v , hα.1]
    · rw [←hα.2]
      fin_cases i <;>
      ( simp [unit_square, Fin.sum_univ_four, v]
        linarith [hα.1 0, hα.1 1, hα.1 2, hα.1 3])
  · intro hx
    -- This part is a little bit annoying. We split it up in some steps.
    have h₁ : 0 < (1 + min (x 0) (x 1) - (x 0) - (x 1)) := by
      cases min_choice (x 0) (x 1) <;> simp_all; linarith [hx 0]
    have h₂ : 0 < min (x 0) (x 1) := by
      cases min_choice (x 0) (x 1) <;> simp_all;
    let a : ℝ := min ((1 + min (x 0) (x 1) - (x 0) - (x 1))) (min (x 0) (x 1) )
    have h₃ : 0 < a := lt_min h₁ h₂
    use fun
          | 0 => (1 + min (x 0) (x 1) - (x 0) - (x 1)) - a/2
          | 1 => x 0 - min (x 0) (x 1) + a/2
          | 2 => min (x 0) (x 1) - a/2
          | 3 => x 1 - min (x 0) (x 1) + a/2
    refine ⟨⟨?_,?_⟩,?_⟩
    · intro i; fin_cases i <;> simp only [Fin.isValue, sub_pos]
      · exact gt_of_ge_of_gt (b := a) (min_le_left _ _) (by linarith)
      · exact add_pos_of_nonneg_of_pos (by simp) (by linarith)
      · exact gt_of_ge_of_gt (b := a) (min_le_right _ _) (by linarith)
      · exact add_pos_of_nonneg_of_pos (by simp) (by linarith)
    · simp [Fin.sum_univ_four]
      ring
    · apply PiLp.ext
      intro i
      fin_cases i <;> simp [Fin.sum_univ_four, unit_square, v]


lemma element_in_boundary_square {x : ℝ²} (hx : x ∈ boundary unit_square) :
    ∃ i, x i = 0 ∨ x i = 1 := by
  by_contra hxn; push_neg at hxn
  have hx₂ := boundary_in_closed hx
  rw [closed_unit_square_eq] at hx₂
  apply boundary_not_in_open hx
  rw [open_unit_square_eq]
  intro i
  constructor
  · exact lt_of_le_of_ne (hx₂ i).1 (hxn i).1.symm
  · exact lt_of_le_of_ne (hx₂ i).2 (hxn i).2


lemma segment_in_boundary_square {x : ℝ²} (hx : x ∈ boundary unit_square)
    : ∃ i, ∀ L, x ∈ open_hull L → closed_hull L ⊆ closed_hull unit_square → (seg_vec L) i = 0 := by
  by_contra hNonzero
  push_neg at hNonzero
  have ⟨i, hxi⟩ := element_in_boundary_square hx
  have ⟨L,hxL,hL, hvec⟩ := hNonzero i
  have ⟨δ,hδ, hδx⟩ := seg_dir_sub hxL
  cases' hxi with hxi hxi
  · specialize hδx (δ * (- Real.sign ((seg_vec L) i))) (by
      simp [abs_mul, abs_of_pos hδ]
      nth_rewrite 2 [←mul_one δ]
      gcongr
      exact real_sign_abs_le
      )
    have ht := hL (open_sub_closed _ hδx)
    rw [closed_unit_square_eq] at ht
    have ht₂ := (ht i).1
    simp [hxi] at ht₂
    linarith [mul_pos hδ (real_sign_mul_self hvec)]
  · specialize hδx (δ * (Real.sign ((seg_vec L) i))) (by
      simp [abs_mul, abs_of_pos hδ]
      nth_rewrite 2 [←mul_one δ]
      gcongr
      exact real_sign_abs_le
      )
    have ht := hL (open_sub_closed _ hδx)
    rw [closed_unit_square_eq] at ht
    have ht₂ := (ht i).2
    simp [hxi] at ht₂
    linarith [mul_pos hδ (real_sign_mul_self hvec)]


/- A version that states that the open_unit_square is open. -/
lemma open_unit_square_open_dir {x : ℝ²} (y : ℝ²) (hx : x ∈ open_hull unit_square) :
    ∃ (ε : ℝ), ε > 0 ∧ ∀ (n : ℕ), x + (1 / (n : ℝ)) • (ε • y) ∈ open_hull unit_square := by
  sorry



lemma el_boundary_square_triangle_dir {x : ℝ²} (hx : x ∈ boundary unit_square):
    ∃ σ ∈ ({-1,1} : Finset ℝ), ∀ (Δ : Triangle), (det Δ ≠ 0) →
    (closed_hull Δ ⊆ closed_hull unit_square) → (∃ i, x ∈ open_hull (Tside Δ i))
    → (∃ εΔ > 0, ∀ y, 0 < y → y ≤ εΔ → x + (σ * y) • (v 1 1) ∈ open_hull Δ) := by
    -- First we produce such triangle
    by_cases hΔ : ∃ Δ, (det Δ ≠ 0) ∧ (closed_hull Δ ⊆ closed_hull unit_square) ∧ (∃ i, x ∈ open_hull (Tside Δ i))
    · have ⟨Δ, hArea, hΔP, ⟨j,hSide⟩⟩ := hΔ
      have ⟨σ, hσ, ⟨δ,hδ, hδx⟩,_⟩  := seg_inter_open (y := v 1 1) hSide hArea ?_
      · use σ, hσ
        intro Δ' hArea' hΔ'P ⟨j',hSide'⟩
        have ⟨σ', hσ', ⟨δ',hδ', hδx'⟩, _⟩  := seg_inter_open (y := v 1 1) hSide' hArea' ?_
        · use δ', hδ'
          convert hδx' using 5
          rw [mul_smul, smul_comm]
          congr
          simp only [mem_insert, mem_singleton] at hσ hσ'
          have hσσ' : σ' = σ ∨ σ' = - σ := by
            cases' hσ with hσ hσ <;> cases' hσ' with hσ' hσ' <;> (rw [hσ, hσ']; simp)
          cases' hσσ' with hσσ' hσσ'
          · exact hσσ'.symm
          · exfalso
            specialize hδx (min δ δ') (lt_min hδ hδ') (min_le_left δ δ')
            specialize hδx' (min δ δ') (lt_min hδ hδ') (min_le_right δ δ')
            rw [hσσ'] at hδx'
            have ⟨i, hL⟩ := segment_in_boundary_square hx
            specialize hL (fun | 0 => x + (δ ⊓ δ') • σ • v 1 1 | 1 => x + (δ ⊓ δ') • -σ • v 1 1) ?_ ?_
            · use fun | 0 => 1/2 | 1 => 1/2
              refine ⟨⟨?_,?_⟩,?_⟩
              · intro i
                fin_cases i <;> simp
              · simp; ring
              · ext i
                fin_cases i <;> (simp; ring)
            · apply closed_hull_convex
              intro i
              fin_cases i
              · exact hΔP (open_sub_closed _ hδx)
              · exact hΔ'P (open_sub_closed _ hδx')
            · unfold seg_vec at hL
              fin_cases i <;>(
                cases' hσ with hσ hσ <;>(
                  simp [hσ, neg_eq_zero] at hL
                  ring_nf at hL
                  try simp [neg_eq_zero,v] at hL
                  linarith [lt_min hδ hδ']
                  ))
        · apply aux_det₂
          · intro this
            rw [seg_vec_zero_iff] at this
            exact (nondegen_triangle_imp_nondegen_side j' hArea') this
          · have ⟨i,hi⟩ := segment_in_boundary_square hx
            exact ⟨i, hi _ hSide' (subset_trans closed_side_sub' hΔ'P)⟩
      · apply aux_det₂
        · intro this
          rw [seg_vec_zero_iff] at this
          exact (nondegen_triangle_imp_nondegen_side j hArea) this
        · have ⟨i,hi⟩ := segment_in_boundary_square hx
          exact ⟨i, hi _ hSide (subset_trans closed_side_sub' hΔP)⟩
    · push_neg at hΔ
      use (1 : ℝ), by simp
      intro Δ hArea hΔP ⟨i,hSide⟩
      exact False.elim (hΔ Δ hArea hΔP i hSide)



lemma segment_triangle_pairing_int (S : Finset Triangle) (hCover : is_disjoint_cover (closed_hull unit_square) (S : Set Triangle))
    (hArea : ∀ Δ ∈ S, det Δ ≠ 0) (L : Segment)
    (hInt: ∀ Δ ∈ S, (open_hull Δ) ∩ (closed_hull L) = ∅)
    (hLunit : open_hull L ⊆ open_hull unit_square) (hv : ∀ Δ ∈ S, ∀ i, Δ i ∉ open_hull L)
  : (S.filter (fun Δ ↦ closed_hull L ⊆ boundary Δ)).card = 2 := by
  -- We first take an element from open_hull L
  have ⟨x, hLx⟩ := open_seg_nonempty L
  -- A useful statement:
  have hU : ∀ Δ ∈ S, x ∉ open_hull Δ := by
    intro Δ hΔ hxΔ
    have this := Set.mem_inter hxΔ (open_sub_closed _ hLx )
    rw [hInt Δ hΔ] at this
    exact this
  -- This x is a member of side i of some triangle Δ.
  have ⟨Δ, hΔ, i, hxi⟩ := cover_mem_side hCover hArea (open_sub_closed _ (hLunit hLx)) hU ?_
  · -- Now it should follow that the closed hull of L is contained in the closed hull of Tside Δ i
    have hLΔ := seg_sub_side (hArea Δ hΔ) hLx hxi (hInt Δ hΔ) (hv Δ hΔ)
    -- We take a vector y that is not in the direction of any side.
    have ⟨y,hy⟩ := perp_vec_exists (Finset.biUnion S (fun Δ ↦ image (fun i ↦ Tside Δ i) (univ))) ?_
    · -- Specialize to the Δᵢ
      have yΔi := hy (Tside Δ i) (by rw [mem_biUnion]; exact ⟨Δ,hΔ,by rw [mem_image]; exact ⟨i, mem_univ _,rfl⟩⟩)
      -- Use this to show that there is a direction of y to move in which does not intersect Δ
      have ⟨σ, hσ, ⟨δ, hδ, hain⟩, haout⟩ := seg_inter_open hxi (hArea Δ hΔ) yΔi
      -- We have an epsilon such that x + (1/n) ε • - σ • y lies inside the open triangle for all n ∈ ℕ
      have ⟨ε,hεPos, hn⟩ := open_unit_square_open_dir (- σ • y) (hLunit hLx)
      -- This gives a map from ℕ to S assigning to each such ℕ a triangle that contains it.
      have hfS : ∀ n : ℕ, ∃ T ∈ S, x + (1 / (n : ℝ)) • ε • -σ • y ∈ closed_hull T := by
        intro n
        have this := (open_sub_closed _ (hn n))
        rw [hCover.1, Set.mem_iUnion₂] at this
        have ⟨T,hT,hT'⟩ := this
        exact ⟨T,hT,hT'⟩
      choose f hfS hfCl using hfS
      -- This means that there is a triangle with infinitely many vectors of the form x + (1 / (n : ℝ)) • ε • -σ • y
      have ⟨Δ', hΔ', hΔ'Inf⟩ := finset_infinite_pigeonhole hfS
      -- First we prove that Δ' ≠ Δ
      have ⟨l,hl,hlZ⟩ := infinite_distinct_el hΔ'Inf 0
      have hMemΔ' := hfCl l
      rw [hl] at hMemΔ'
      have hΔneq : Δ' ≠ Δ := by
        by_contra hΔeq
        rw [hΔeq] at hMemΔ'
        apply haout ((1/ (l : ℝ) * ε)) (by field_simp)
        convert hMemΔ' using 2
        simp [mul_smul]
      -- Then we prove that x ∈ closed_hull Δ'
      have hxΔ' := closed_triangle_is_closed_dir (x := x) (y := ε • -σ • y) (hArea Δ' hΔ') (by
        refine Set.Infinite.mono ?_ hΔ'Inf
        intro m _
        have _ := hfCl m
        simp_all
        )
      -- This means that x lies in some side of Δ'
      have ⟨i',hi'⟩ := el_in_boundary_imp_side (hArea Δ' hΔ') (Set.mem_diff_of_mem hxΔ' (fun d ↦ hU Δ' hΔ' d)) (fun i ht ↦ hv Δ' hΔ' i (by rwa [←ht]))
      -- This again means that L lies completely in Tside Δ' i
      have hLΔ' := seg_sub_side (hArea Δ' hΔ') hLx hi' (hInt Δ' hΔ') (hv Δ' hΔ')
      -- We now have our two elements that should give the cardinality 2.
      rw [card_eq_two]
      use Δ', Δ, hΔneq
      ext Δ''
      constructor
      · -- The hard part of the proof continues here.
        -- We have to show that if there is a third triangle that it intersects one of the triangles.
        intro hΔ''
        rw [mem_filter] at hΔ''
        have ⟨hΔ'', hLΔ''⟩ := hΔ''
        have ⟨i'',hi''⟩ := el_in_boundary_imp_side (hArea Δ'' hΔ'') (hLΔ'' (open_sub_closed _ hLx)) (fun i ht ↦ hv Δ'' hΔ'' i (by rwa [←ht]))
        -- We define σ' and σ''
        have yΔi' := hy (Tside Δ' i') (by rw [mem_biUnion]; exact ⟨Δ',hΔ',by rw [mem_image]; exact ⟨i', mem_univ _,rfl⟩⟩)
        have ⟨σ', hσ', ⟨δ',hδ', hain'⟩, haout'⟩ := seg_inter_open hi' (hArea Δ' hΔ') yΔi'
        have yΔi'' := hy (Tside Δ'' i'') (by rw [mem_biUnion]; exact ⟨Δ'',hΔ'',by rw [mem_image]; exact ⟨i'', mem_univ _,rfl⟩⟩)
        have ⟨σ'', hσ'', ⟨δ'',hδ'', hain''⟩, haout''⟩ := seg_inter_open hi'' (hArea Δ'' hΔ'') yΔi''
        -- First we show that σ ≠ σ' The following argument is repeated
        -- three times and could use its own lemma
        have σneq : σ ≠ σ' := by
          intro σeq
          rw [σeq] at hain
          specialize hain (min δ δ') (lt_min hδ hδ') (min_le_left δ δ')
          specialize hain' (min δ δ') (lt_min hδ hδ') (min_le_right δ δ')
          exact hΔneq (is_cover_open_el_imp_eq hCover.2 hΔ' hΔ hain' hain)
        have σ''mem : σ'' = σ ∨ σ'' = σ' := by
          simp only [mem_insert, mem_singleton] at hσ hσ' hσ''
          cases' hσ with t t <;> cases' hσ' with t' t' <;> cases' hσ'' with t'' t'' <;> (
            rw [t,t',t'']
            rw [t,t'] at σneq
            tauto)
        cases' σ''mem with h h
        · have hl : Δ'' = Δ := by
            by_contra hneq
            rw [h] at hain''
            specialize hain (min δ δ'') (lt_min hδ hδ'') (min_le_left δ δ'')
            specialize hain'' (min δ δ'') (lt_min hδ hδ'') (min_le_right δ δ'')
            exact hneq (is_cover_open_el_imp_eq hCover.2 hΔ'' hΔ hain'' hain)
          simp only [hl, mem_insert, mem_singleton, or_true]
        · have hl : Δ'' = Δ' := by
            by_contra hneq
            rw [h] at hain''
            specialize hain' (min δ' δ'') (lt_min hδ' hδ'') (min_le_left δ' δ'')
            specialize hain'' (min δ' δ'') (lt_min hδ' hδ'') (min_le_right δ' δ'')
            exact hneq (is_cover_open_el_imp_eq hCover.2 hΔ'' hΔ' hain'' hain')
          simp only [hl, mem_insert, mem_singleton, true_or]
      · intro hΔ''; simp at hΔ''
        cases' hΔ'' with hΔ'' hΔ'' <;> (rw [hΔ'']; simp)
        · exact ⟨hΔ', fun _ a ↦ (side_in_boundary (hArea Δ' hΔ') i') (hLΔ' a)⟩
        · exact ⟨hΔ, fun _ a ↦ (side_in_boundary (hArea Δ hΔ) i) (hLΔ a)⟩
    · intro L hL
      simp_rw [mem_biUnion, mem_image] at hL
      have ⟨T,TS,i',_,hTL⟩ := hL
      rw [←hTL]
      exact nondegen_triangle_imp_nondegen_side _ (hArea T TS)
  · intro i Δ hΔ hxΔ
    rw [hxΔ] at hLx
    exact hv Δ hΔ i hLx


lemma segment_triangle_pairing_boundary (S : Finset Triangle) (hCover : is_disjoint_cover (closed_hull unit_square) (S : Set Triangle))
    (hArea : ∀ Δ ∈ S, det Δ ≠ 0) (L : Segment) (hL : L 0 ≠ L 1)
    (hInt: ∀ Δ ∈ S, (open_hull Δ) ∩ (closed_hull L) = ∅)
    (hLunit : open_hull L ⊆ boundary unit_square) (hv : ∀ Δ ∈ S, ∀ i, Δ i ∉ open_hull L)
  : (S.filter (fun Δ ↦ closed_hull L ⊆ boundary Δ)).card = 1 := by
  -- We first take an element from open_hull L
  have ⟨x, hLx⟩ := open_seg_nonempty L
  -- The point x is not in any open triangle:
  have hU : ∀ Δ ∈ S, x ∉ open_hull Δ := by
    intro Δ hΔ hxΔ
    have this := Set.mem_inter hxΔ (open_sub_closed _ hLx )
    rw [hInt Δ hΔ] at this
    exact this
  -- The point x is also not a vertex of any triangle
  have hxNvtx : ∀ (i : Fin 3), ∀ Δ ∈ S, x ≠ Δ i := by
    intro i Δ hΔ hxΔ
    rw [hxΔ] at hLx
    exact hv Δ hΔ i hLx
  -- This x is a member of side i of some triangle Δ.
  have ⟨Δ, hΔ, i, hxi⟩ := cover_mem_side hCover hArea (boundary_sub_closed unit_square (hLunit hLx)) hU hxNvtx
  -- The closed hull of L is contained in the closed hull of Tside Δ i
  have hLΔ := seg_sub_side (hArea Δ hΔ) hLx hxi (hInt Δ hΔ) (hv Δ hΔ)
  -- We will prove that Δ is the only triangle containing L in its boundary
  refine card_eq_one.mpr ⟨Δ,?_⟩
  simp_rw [eq_singleton_iff_unique_mem, mem_filter]
  constructor
  · exact ⟨hΔ, subset_trans hLΔ (side_in_boundary (hArea Δ hΔ) i)⟩
  · intro Δ' ⟨hΔ',hΔ'sub⟩
    -- There is a side i' such that
    have ⟨i',hi'⟩ := segment_in_boundary_imp_in_side (hArea Δ' hΔ') hΔ'sub
    -- Pick the direction for which the vector (1,1) points into the square
    have ⟨σ, hσval, hσ⟩ := el_boundary_square_triangle_dir (hLunit hLx)
    -- Specialize to the triangles Δ and Δ'
    have ⟨ε, hε, hεΔ⟩ := hσ Δ (hArea Δ hΔ) (is_cover_sub hCover.1 Δ hΔ) ⟨i,hxi⟩
    have ⟨ε', hε', hεΔ'⟩ := hσ Δ' (hArea Δ' hΔ') (is_cover_sub hCover.1 Δ' hΔ') ⟨i',open_segment_sub' hi' hL hLx⟩
    specialize hεΔ (min ε ε') (lt_min hε hε') (min_le_left ε ε')
    specialize hεΔ' (min ε ε') (lt_min hε hε') (min_le_right ε ε')
    exact is_cover_open_el_imp_eq hCover.2 hΔ' hΔ hεΔ' hεΔ
