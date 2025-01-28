import Mathlib
import Mathlib.Tactic
import FormalBook.sperner.simplex_basic
import FormalBook.sperner.miscellaneous

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "Triangle" => Fin 3 → ℝ²
local notation "Segment" => Fin 2 → ℝ²

open Classical
open BigOperators
open Finset


/-
  This file includes the lemmas that involve Segments and Triangles.

  It includes the definition of det T, where T is a triangle.
-/

/- Basic definitions. -/

/- 'Determinant' of a triangle. -/
def det (T : Triangle) : ℝ
  := (T 0 1 - T 1 1) * (T 2 0) + (T 1 0 - T 0 0) * (T 2 1) + ((T 0 0) * (T 1 1) - (T 1 0) * (T 0 1))

def det₂ (x y : ℝ²) : ℝ := x 0 * y 1 - x 1 * y 0

/- The vector pointing from the start of the segment to the end.-/
noncomputable def seg_vec (L : Segment) : ℝ² := L 1 - L 0

def sign_seg (L : Segment) (v : ℝ²) : ℝ := det (fun | 0 => L 0 | 1 => L 1 | 2 => v)

def to_segment (a b : ℝ²) : Segment := fun | 0 => a | 1 => b

def reverse_segment (L : Segment) : Segment := to_segment (L 1) (L 0)

def colin (u v w : ℝ²) : Prop := u ≠ w ∧ v ∈ open_hull (to_segment u w)

/- Tside i defines the 'directed' opposite side of T i.-/
def Tside (T : Triangle) : Fin 3 → Segment := fun
  | 0 => (fun | 0 => T 1 | 1 => T 2)
  | 1 => (fun | 0 => T 2 | 1 => T 0)
  | 2 => (fun | 0 => T 0 | 1 => T 1)

/- Barycentric coordinates on triangle T. -/
noncomputable def Tco (T : Triangle) (x : ℝ²) : Fin 3 → ℝ :=
  fun i ↦ (sign_seg (Tside T i) x) / det T

/-
  This definition is sometimes used, but sometimes isn't.
  To do: Make this more uniform.
-/
noncomputable def Oside (T : Triangle) (i : Fin 3) := seg_vec (Tside T i)






/- Basic lemmas about det₂.-/
lemma det₂_mul_last {x y : ℝ²} (a : ℝ)
  : det₂ x (a • y) = a * det₂ x y := by
  simp [det₂]; ring

lemma aux_det₂ {L : ℝ²} (hL : L ≠ 0) (hi : ∃ i, L i = 0) : det₂ L (v 1 1) ≠ 0 := by
  by_contra hz
  refine hL ?_
  ext j
  have ⟨i, hi⟩ := hi
  fin_cases i <;> (
    simp at hi
    simp [det₂, hi] at hz
    fin_cases j <;> (simp_all [v])
  )




/- Segments -/

lemma open_segment_sub {L₁ L₂ : Segment} (hsub: ∀ i : Fin 2, L₁ i ∈ closed_hull L₂) (hL₁ : L₁ 0 ≠ L₁ 1) :
    open_hull L₁ ⊆ open_hull L₂ := by
  intro x ⟨α,hα,hx⟩
  refine (Set.mem_image (fun α ↦ ∑ i : Fin 2, α i • L₂ i) (open_simplex 2) x).mpr ?_
  have h1: ∃ α₁ ∈ closed_simplex 2, L₁ 0 = ∑ i : Fin 2, α₁ i • L₂ i := by
    rcases hsub 0 with ⟨β, hβ₁, β₁₀⟩
    have h1': (fun α ↦ ∑ i : Fin 2, α i • L₂ i) β = ∑ i : Fin 2, β i • L₂ i := by
      simp only [Fin.sum_univ_two, Fin.isValue]
    have h1'': ∑ i : Fin 2, β i • L₂ i = L₁ 0 := by
      rw [←h1']
      exact β₁₀
    use β
    constructor
    · apply hβ₁
    · exact h1''.symm
  have h2: ∃ α₂ ∈ closed_simplex 2, L₁ 1 = ∑ i : Fin 2, α₂ i • L₂ i := by
    rcases hsub 1 with ⟨β, hβ₁, β₁₀⟩
    have h2': (fun α ↦ ∑ i : Fin 2, α i • L₂ i) β = ∑ i : Fin 2, β i • L₂ i := by
      simp only [Fin.sum_univ_two, Fin.isValue]
    have h2'': ∑ i : Fin 2, β i • L₂ i = L₁ 1 := by
      rw [←h2']
      exact β₁₀
    use β
    constructor
    · apply hβ₁
    · exact h2''.symm
  rcases h1 with ⟨α₁,hα₁,hL₁₀⟩
  rcases h2 with ⟨α₂,hα₂,hL₁₁⟩
  have pos : ∀ i, 0 < α i := by
    apply hα.1
  have pos1 : ∀ i, 0 ≤  α₁ i := by
    apply hα₁.1
  have pos2 : ∀ i, 0 ≤ α₂ i := by
    apply hα₂.1
  let x₁ : Fin 2 → ℝ := fun i => match i with
    | 0 => (α 0 * α₁ 0 + α 1 * α₂ 0)
    | 1 => (α 0 * α₁ 1 + α 1 * α₂ 1)
  have hαx₁ : x₁ ∈ open_simplex 2 := by
    constructor
    have x₁0_pos : x₁ 0 > 0 := by
      simp [x₁, pos, pos1, pos2]
      by_contra h
      simp at h
      have p : α₁ 0 = 0 := by
        by_contra hα₁0
        have p' : α 0 * α₁ 0 + α 1 * α₂ 0 > 0 := by
          simp only [add_pos_of_pos_of_nonneg,mul_pos (pos 0),lt_of_le_of_ne (pos1 0) (Ne.symm hα₁0),
          mul_nonneg (pos 1).le (hα₂.1 0)]
        linarith [p', h]
      have q : α₂ 0 = 0 := by
          by_contra hα₂0
          have q' : α 0 * α₁ 0 + α 1 * α₂ 0 > 0 := by
            simp only [add_pos_of_nonneg_of_pos, mul_nonneg (pos 0).le (hα₁.1 0), mul_pos (pos 1),
            lt_of_le_of_ne (pos2 0) (Ne.symm hα₂0)]
          linarith [q', h]
      have r : α₁ 1 = 1 := by
        by_contra
        rcases hα₁ with ⟨_,hα₁₂⟩
        rw [Fin.sum_univ_two, p, zero_add] at hα₁₂
        contradiction
      have  s : α₂ 1 = 1 := by
        by_contra
        rcases hα₂ with ⟨_,hα₂₂⟩
        rw [Fin.sum_univ_two, q, zero_add] at hα₂₂
        contradiction
      simp [p,q,r,s] at hL₁₀ hL₁₁
      rw [← hL₁₁] at hL₁₀
      absurd hL₁
      exact hL₁₀
    have x₁1_pos : x₁ 1 > 0 := by
      simp [x₁, pos, pos1, pos2]
      by_contra h
      simp only [Fin.isValue, not_lt] at h
      have t : α₁ 1 = 0 := by
        by_contra hα₁0
        have t' : α 0 * α₁ 1 + α 1 * α₂ 1 > 0 := by
          simp only [add_pos_of_pos_of_nonneg,mul_pos (pos 0),lt_of_le_of_ne (pos1 1) (Ne.symm hα₁0),
          mul_nonneg (pos 1).le (hα₂.1 1)]
        linarith [t', h]
      have u : α₂ 1 = 0 := by
          by_contra hα₂0
          have u' : α 0 * α₁ 1 + α 1 * α₂ 1 > 0 := by
            simp only [add_pos_of_nonneg_of_pos, mul_nonneg (pos 0).le (hα₁.1 1), mul_pos (pos 1),
            lt_of_le_of_ne (pos2 1) (Ne.symm hα₂0)]
          linarith [u', h]
      have v : α₁ 0 = 1 := by
        by_contra
        rcases hα₁ with ⟨_,hα₁₂⟩
        rw [Fin.sum_univ_two, t, add_zero] at hα₁₂
        contradiction
      have  w : α₂ 0 = 1 := by
        by_contra
        rcases hα₂ with ⟨_,hα₂₂⟩
        rw [Fin.sum_univ_two, u, add_zero] at hα₂₂
        contradiction
      simp [t,u,v,w] at hL₁₀ hL₁₁
      rw [← hL₁₁] at hL₁₀
      absurd hL₁
      exact hL₁₀
    · exact fun i ↦ by
        fin_cases i
        all_goals (simp [x₁, x₁0_pos, x₁1_pos, pos, pos1, pos2])
    · simp only [x₁, hα.2, hα₁.2, hα₂.2]
      rcases hα with ⟨_,h₂⟩
      rcases hα₁ with ⟨hα₁₁,hα₁₂⟩
      rcases hα₂ with ⟨hα₂₁,hα₂₂⟩
      simp [← add_assoc, add_comm, ← mul_add, add_assoc]
      rw [Fin.sum_univ_two] at hα₁₂ hα₂₂ h₂
      calc
        α 0 * α₁ 0 + (α 1 * α₂ 0 + (α 0 * α₁ 1 + α 1 * α₂ 1)) = α 0 * (α₁ 0 + α₁ 1) + α 1 * (α₂ 0 + α₂ 1) := by ring
        _ = 1 := by simp [hα₁₂,hα₂₂, mul_one, mul_one, h₂]
  use x₁
  constructor
  · exact hαx₁
  · simp only [Fin.sum_univ_two, Fin.isValue, hL₁₀, smul_add, hL₁₁, ← add_assoc, add_comm] at hx
    simp only [Fin.isValue, Fin.sum_univ_two, add_smul, mul_smul, ← add_assoc, x₁]
    exact hx

lemma open_segment_sub' {L₁ L₂ : Segment} (hsub: closed_hull L₁ ⊆ closed_hull L₂)
    (hL₁ : L₁ 0 ≠ L₁ 1) : open_hull L₁ ⊆ open_hull L₂ :=
  open_segment_sub (fun _ ↦ (hsub corner_in_closed_hull)) hL₁


lemma boundary_seg {L : Segment} (hL : L 0 ≠ L 1)
    : boundary L = image (fun i ↦ L i) (univ : Finset (Fin 2)) := by
  ext x
  constructor
  · intro hx
    have ⟨α,hα,hαx⟩ := boundary_in_closed hx
    have α_non_zero : ∃ i, α i = 0 := by
      by_contra hcontra; push_neg at hcontra
      apply boundary_not_in_open hx
      exact ⟨α,⟨fun i ↦ lt_of_le_of_ne (hα.1 i) (hcontra i).symm,hα.2⟩ ,hαx⟩
    sorry
  · sorry


lemma sign_seg_line (L : Segment) (x y : ℝ²) (a : ℝ) :
    sign_seg L (x + a • y) = (sign_seg L x) + a * (det₂ (seg_vec L) y) := by
  simp [sign_seg, det₂, det, seg_vec]; ring

lemma seg_vec_zero_iff (L : Segment) : seg_vec L = 0 ↔ L 0 = L 1 := by
  rw [seg_vec, sub_eq_zero]
  exact eq_comm

lemma seg_dir_sub {L : Segment} {x : ℝ²} (hxL : x ∈ open_hull L) :
    ∃ δ > 0, ∀ (a : ℝ), |a| ≤ δ → x + a • seg_vec L ∈ open_hull L := by

  sorry

lemma seg_vec_co {L : Segment} {x y : ℝ²} (hx : x ∈ closed_hull L) (hy : y ∈ closed_hull L)
  : ∃ a : ℝ, y = x + a • seg_vec L := by

  sorry

lemma open_seg_nonempty (L : Segment) : ∃ x, x ∈ open_hull L :=
  open_pol_nonempty (by linarith) L


lemma perp_vec_exists (Lset : Finset Segment) (hLset : ∀ L ∈ Lset, L 0 ≠ L 1)
    : ∃ y : ℝ², ∀ L ∈ Lset, det₂ (seg_vec L) y ≠ 0 := by
  have ⟨y₁, hy₁⟩ := Infinite.exists_not_mem_finset (image (fun L ↦ seg_vec L 1 / seg_vec L 0) Lset)
  use fun | 0 => 1 | 1 => y₁
  intro L hL
  simp [det₂]
  intro hContra
  by_cases h : seg_vec L 0 = 0
  · apply hLset L hL
    rw [←seg_vec_zero_iff]
    exact PiLp.ext (fun i ↦ by fin_cases i <;> simp_all)
  · apply hy₁
    rw [mem_image]
    refine ⟨L,hL,?_⟩
    field_simp
    linarith


@[simp]
lemma reverse_segment_to_segment {u v : ℝ²}
  : reverse_segment (to_segment u v) = to_segment v u := rfl

@[simp]
lemma reverse_segment_involution {L : Segment}
    : reverse_segment (reverse_segment L) = L := by
  ext i _
  fin_cases i <;> simp [reverse_segment, to_segment]


lemma reverse_segment_closed_hull {L : Segment}
    : closed_hull (reverse_segment L) = closed_hull L := by
  have haux : ∀ L', closed_hull L' ⊆ closed_hull (reverse_segment L') := by
    intro L x ⟨α,hα,hαx⟩
    refine ⟨fun | 0 => α 1 | 1 => α 0, ⟨?_,?_⟩ ,?_⟩
    · exact fun i ↦ by fin_cases i <;> linarith [hα.1 0, hα.1 1]
    · simp_rw [←hα.2, Fin.sum_univ_two, add_comm]
    · simp_rw [←hαx, Fin.sum_univ_two, reverse_segment, to_segment, add_comm]
  exact Set.Subset.antisymm (haux (reverse_segment L)) (haux L)

lemma reverse_segment_open_hull {L : Segment}
    : open_hull (reverse_segment L) = open_hull L := by
  have haux : ∀ L', open_hull L' ⊆ open_hull (reverse_segment L') := by
    intro L x ⟨α,hα,hαx⟩
    refine ⟨fun | 0 => α 1 | 1 => α 0, ⟨?_,?_⟩ ,?_⟩
    · exact fun i ↦ by fin_cases i <;> linarith [hα.1 0, hα.1 1]
    · simp_rw [←hα.2, Fin.sum_univ_two, add_comm]
    · simp_rw [←hαx, Fin.sum_univ_two, reverse_segment, to_segment, add_comm]
  exact Set.Subset.antisymm (by convert haux (reverse_segment L); exact reverse_segment_involution.symm) (haux L)


lemma colin_reverse {u v w : ℝ²} (h : colin u v w) : colin w v u := by
  have ⟨h₁,h₂⟩ := h
  exact ⟨h₁.symm, by rwa [←reverse_segment_open_hull, reverse_segment_to_segment]⟩





/- Triangles -/

/-
  Given two distinct i,j from Fin 3 this will return the unique element not equal to i and j.
  If i = j it returns the junk value i.
-/
def last_index : Fin 3 → Fin 3 → Fin 3 := fun
  | 0 => (fun | 0 => 0 | 1 => 2 | 2 => 1)
  | 1 => (fun | 0 => 2 | 1 => 1 | 2 => 0)
  | 2 => (fun | 0 => 1 | 1 => 0 | 2 => 2)

lemma linear_combination_det_last {n : ℕ} {x y : ℝ²} {P : Fin n → ℝ²} {α : Fin n → ℝ}
    (hα : ∑ i, α i = 1) :
  det (fun | 0 => x | 1 => y | 2 => (∑ i, α i • P i)) =
  ∑ i, (α i * det (fun | 0 => x | 1 => y | 2 => (P i))) := by
  simp [det, left_distrib, sum_add_distrib, sum_apply _, mul_sum, ←sum_mul, hα]
  congr <;> (ext; ring)



/- Lemmas about the barycentric coordinates -/

lemma Tco_sum {T : Triangle} (hdet : det T ≠ 0) (x : ℝ²) : ∑ i, Tco T x i = 1 := by
  apply mul_cancel hdet
  simp_rw [mul_sum, Tco, Fin.sum_univ_three, mul_div_cancel₀ _ hdet, sign_seg, det, Tside]
  ring

lemma Tco_linear {n : ℕ} {T : Triangle} {P : Fin n → ℝ²} {α : Fin n → ℝ}
    (hα : ∑ i, α i = 1) (k : Fin 3): Tco T (∑ i, (α i) • (P i)) k =  ∑ i, α i * Tco T (P i) k := by
  fin_cases k <;> (
  simp [Tco, sign_seg, linear_combination_det_last hα,sum_div]
  congr; funext _; ring)

lemma Tco_basis_diag {T : Triangle} (hdet : det T ≠ 0) {i : Fin 3} :
    Tco T (T i) i = 1 := by
  fin_cases i<;>(
    apply mul_cancel hdet
    simp [Tco, mul_div_cancel₀ _ hdet]
    simp [sign_seg,det, Tside]
  ) <;> ring

lemma Tco_basis_off_diag {T : Triangle} {i j: Fin 3} (hij : i ≠ j) :
    Tco T (T i) j = 0 := by
  fin_cases i <;> fin_cases j
  all_goals (try tauto)
  all_goals (
    simp [Tco]; left
    simp [sign_seg, det, Tside]; ring)

lemma Tco_sum_val {T : Triangle} (hdet : det T ≠ 0) {α : Fin 3 → ℝ} (hα : ∑i, α i = 1) (k : Fin 3) :
    Tco T (∑ i, (α i) • (T i)) k = α k := by
  rw [Tco_linear hα, Fin.sum_univ_three]
  fin_cases k <;> simp [Tco_basis_diag hdet, Tco_basis_off_diag]

lemma Tco_sum_self {T : Triangle} (hdet : det T ≠ 0) (x : ℝ²) :
    ∑ i, (Tco T x i) • (T i) = x := by
  apply smul_cancel hdet
  simp [smul_sum, smul_smul, Fin.sum_univ_three, mul_div_cancel₀ _ hdet, Tco]
  simp [sign_seg, det, Tside]
  exact PiLp.ext (fun i ↦ by fin_cases i <;> (simp; ring))

lemma closed_triangle_iff {T : Triangle} (hdet : det T ≠ 0) {x : ℝ²} :
    x ∈ closed_hull T ↔ ∀ i, 0 ≤ Tco T x i := by
  constructor
  · exact fun ⟨α,hα,hαx⟩ ↦ by simp_rw [←hαx, Tco_sum_val hdet hα.2]; exact hα.1
  · exact fun hco ↦ ⟨Tco T x, ⟨hco, Tco_sum hdet x⟩, Tco_sum_self hdet x⟩

lemma open_triangle_iff {T : Triangle} (hdet : det T ≠ 0) {x : ℝ²} :
    x ∈ open_hull T ↔ ∀ i, 0 < Tco T x i := by
  constructor
  · exact fun ⟨α,hα,hαx⟩ ↦ by simp_rw [←hαx, Tco_sum_val hdet hα.2]; exact hα.1
  · exact fun hco ↦ ⟨Tco T x, ⟨hco, Tco_sum hdet x⟩, Tco_sum_self hdet x⟩

lemma two_co_zero_imp_corner_co {T : Triangle} {i j : Fin 3} {x : ℝ²} (hdet : det T ≠ 0)
    (hij : i ≠ j) (hi : Tco T x i = 0) (hj : Tco T x j = 0) :
    Tco T x (last_index i j) =  1 := by
  rw [←Tco_sum hdet x, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp_all [last_index]

lemma two_co_zero_imp_corner {T : Triangle} {i j : Fin 3} {x : ℝ²} (hdet : det T ≠ 0)
  (hij : i ≠ j) (hi : Tco T x i = 0) (hj : Tco T x j = 0) :
    x = T (last_index i j) := by
  have hk := two_co_zero_imp_corner_co hdet hij hi hj
  rw [←Tco_sum_self hdet x, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp_all [last_index]

lemma Tco_line {T : Triangle} {i : Fin 3} (x y : ℝ²) (a : ℝ) :
    Tco T (x  + a • y) i = Tco T x i + a * (det₂ (Oside T i) y) / det T := by
  rw [Tco, sign_seg_line, add_div, ←Tco, ←Oside]


/- Lemmas about elements in the side of a triangle. -/
lemma nondegen_triangle_imp_nondegen_side {T : Triangle} (i : Fin 3) (hdet : det T ≠ 0):
    Tside T i 0 ≠ Tside T i 1 :=
  fun hS ↦ hdet (by fin_cases i <;> (simp [Tside] at hS; simp [det, hS]) <;> ring)

lemma mem_closed_side {T : Triangle} (hdet : det T ≠ 0) {x : ℝ²} (hx : x ∈ closed_hull T) (i : Fin 3) :
    Tco T x i = 0 ↔ x ∈ closed_hull (Tside T i) := by
  constructor
  · intro hTco
    use (fun | 0 => Tco T x (i + 1) | 1 => Tco T x (i + 2))
    refine ⟨⟨?_,?_⟩,?_⟩
    · exact fun j ↦ by fin_cases j <;> exact (closed_triangle_iff hdet).1 hx _
    · simp_rw [←Tco_sum hdet x, Fin.sum_univ_three, Fin.sum_univ_two]
      fin_cases i <;> (simp [hTco, add_comm] at *)
    · nth_rw 3 [←Tco_sum_self hdet x]
      fin_cases i <;> (simp [Fin.sum_univ_three, hTco, Tside, add_comm] at *)
  · intro ⟨α, hα, hαx⟩
    rw [←hαx, Tco_linear hα.2]
    fin_cases i <;> (simp [Tside, Tco_basis_off_diag])

lemma closed_side_sub {T : Triangle} {x : ℝ²} {i : Fin 3} (hx : x ∈ closed_hull (Tside T i)) :
    x ∈ closed_hull T := by
  refine closed_hull_convex ?_ hx
  intro j
  fin_cases i <;> fin_cases j <;> simp [Tside, simplex_vertex_in_simplex]

lemma closed_side_sub' {T : Triangle} {i : Fin 3} :
    closed_hull (Tside T i) ⊆ closed_hull T := fun _ ↦ closed_side_sub

lemma closed_side_to_co {T : Triangle} (hdet : det T ≠ 0) {x : ℝ²} {i : Fin 3} (hx : x ∈ closed_hull (Tside T i)) :
    Tco T x i = 0 := (mem_closed_side hdet (closed_side_sub hx) _).2 hx

lemma mem_open_side {T : Triangle} (hdet : det T ≠ 0) {x : ℝ²} (hx : x ∈ closed_hull T) (i : Fin 3) :
    (Tco T x i = 0 ∧ ∀ j, j ≠ i → 0 < Tco T x j) ↔ x ∈ open_hull (Tside T i) := by
  constructor
  · intro ⟨hTco, hall⟩
    -- This is basically the same proof as the closed version.
    use (fun | 0 => Tco T x (i + 1) | 1 => Tco T x (i + 2))
    refine ⟨⟨?_,?_⟩,?_⟩
    · exact fun j ↦ by fin_cases j <;> simp [hall]
    · simp_rw [←Tco_sum hdet x, Fin.sum_univ_three, Fin.sum_univ_two]
      fin_cases i <;> (simp [hTco, add_comm] at *)
    · nth_rw 3 [←Tco_sum_self hdet x]
      fin_cases i <;> (simp [Fin.sum_univ_three, hTco, Tside, add_comm] at *)
  · intro hxOpen
    have hTcoi : Tco T x i = 0 := by
      rw [mem_closed_side hdet hx]
      exact open_sub_closed _ hxOpen
    refine ⟨hTcoi, ?_⟩
    by_contra hEx;
    push_neg at hEx
    have ⟨j,hjneq,hTcoj'⟩ := hEx
    have hTcoj : Tco T x j = 0 := by
      linarith [hTcoj', (closed_triangle_iff hdet).1 hx j]
    refine boundary_not_in_open (P := Tside T i) ?_ hxOpen
    rw [boundary_seg (nondegen_triangle_imp_nondegen_side i hdet), fin2_im, two_co_zero_imp_corner hdet hjneq hTcoj hTcoi]
    simp
    fin_cases i <;> fin_cases j <;> tauto

lemma mem_open_side_other_co {T : Triangle} (hdet : det T ≠ 0) {x : ℝ²}  {i : Fin 3} (hxOpen : x ∈ open_hull (Tside T i))
  : ∀ j, j ≠ i → 0 < Tco T x j := by
  rw [←(mem_open_side hdet (closed_side_sub (open_sub_closed _ hxOpen)))] at hxOpen
  exact hxOpen.2


/- Boundary of a triangle. -/

lemma boundary_iff {T : Triangle} (hdet : det T ≠ 0) {x : ℝ²} (hx : x ∈ closed_hull T) :
    x ∈ boundary T ↔ ∃ i, Tco T x i = 0 := by
  constructor
  · intro hxB
    by_contra hAll
    push_neg at hAll
    apply ((Set.mem_diff _).mp hxB).2
    rw [open_triangle_iff hdet]
    rw [closed_triangle_iff hdet] at hx
    exact fun i ↦ lt_of_le_of_ne (hx i) (hAll i).symm
  · intro ⟨i,hi⟩
    rw [boundary, Set.mem_diff]
    refine ⟨hx,?_⟩
    intro hxOpen
    rw [open_triangle_iff hdet] at hxOpen
    linarith [hi, hxOpen i]

lemma side_in_boundary {T : Triangle} (hdet : det T ≠ 0) (i : Fin 3) :
    closed_hull (Tside T i) ⊆ boundary T := by
  intro x hx
  rw [boundary_iff hdet (closed_side_sub hx)]
  exact ⟨i, closed_side_to_co hdet hx⟩

lemma boundary_is_union_sides {T : Triangle} (hdet : det T ≠ 0)
    : boundary T = ⋃ i, closed_hull (Tside T i) := by
  ext x
  constructor
  · intro hx
    have ⟨i,_⟩ := (boundary_iff hdet (Set.mem_of_mem_diff hx)).1 hx
    exact Set.mem_iUnion.mpr ⟨i, by rwa [←mem_closed_side hdet (Set.mem_of_mem_diff hx) i]⟩
  · intro hx
    have ⟨_,hx⟩ := Set.mem_iUnion.1 hx
    exact side_in_boundary hdet _ hx

lemma el_boundary_imp_side {T : Triangle} (hdet : det T ≠ 0) {x : ℝ²} (hx : x ∈ boundary T)
    : ∃ i, x ∈ closed_hull (Tside T i) := by
  rw [boundary_is_union_sides hdet] at hx
  exact Set.mem_iUnion.mp hx

lemma el_in_boundary_imp_side {T : Triangle} {x : ℝ²} (hdet : det T ≠ 0)
    (hx : x ∈ boundary T) (hv : ∀ i, x ≠ T i) : ∃ i, x ∈ open_hull (Tside T i) := by
  have hxClosed := (Set.mem_of_mem_diff hx)
  have ⟨i,hi⟩ := (boundary_iff hdet hxClosed).1 hx
  use i
  rw [←mem_open_side hdet hxClosed]
  refine ⟨hi,?_⟩
  intro j hji
  by_contra hj
  apply hv (last_index j i)
  refine two_co_zero_imp_corner hdet hji  ?_ hi
  linarith [hj, (closed_triangle_iff hdet).1 hxClosed j]


/-
  We are given an x on the boundary of a nondegenerate triangle with x not one of the
  vertices of the triangle and a vector y not co-linear with the part of the boundary that
  y is on. There is a σ ∈ {±1} such that x + ε σ y lies in the triangle for small ε > 0 and
  x - a σ y does not (for all a > 0).
-/
lemma seg_inter_open {T : Triangle} {x y : ℝ²} {i : Fin 3}
  (hxT : x ∈ open_hull (Tside T i)) (hdet: det T ≠ 0)
  (hdet₂ : det₂ (seg_vec (Tside T i)) y ≠ 0) :
  ∃ σ ∈ ({-1,1} : Finset ℝ), (∃ δ > 0, (∀ a : ℝ,
    (0 < a → a ≤ δ → x + a • σ • y ∈ open_hull T))) ∧ ∀ a : ℝ, 0 < a → x + a • (- σ) • y ∉ closed_hull T := by
  use Real.sign (det T * det₂ (Oside T i) y)
  constructor
  · rw [real_sign_mul,Oside]
    cases' Real.sign_apply_eq_of_ne_zero  _ hdet <;>
    cases' Real.sign_apply_eq_of_ne_zero  _ hdet₂ <;>
    simp_all
  · constructor
    · simp_rw [open_triangle_iff hdet, Tco_line, ←and_imp, forall_in_swap_special]
      rw [forall_exists_pos_swap]
      · intro j
        by_cases hij : j = i
        · use 1, by norm_num -- Junk value
          intro a ⟨hapos, _⟩
          rw [hij, closed_side_to_co hdet (open_sub_closed _ hxT), zero_add, mul_div_assoc]
          apply mul_pos hapos
          rw [det₂_mul_last, real_sign_mul, mul_assoc, mul_div_right_comm]
          exact mul_pos (real_sign_div_self hdet) (real_sign_mul_self (by rwa [Oside]))
        · have ⟨δ,hδpos, hδa⟩ := real_interval_δ (det₂ (Oside T j) ((det T * det₂ (Oside T i) y).sign • y) / det T) (mem_open_side_other_co hdet hxT j  hij)
          use δ, hδpos
          intro a ⟨hapos,haup⟩
          convert hδa a (by rwa [abs_of_pos hapos]) using 1
          field_simp
      · intro δ j ha δ' hδ' a ⟨ha'1, ha'2⟩
        apply ha
        simp_all only [ne_eq, and_imp, true_and, Preorder.le_trans a δ' δ ha'2 hδ']
    · intro a hapos hacl
      simp_rw [closed_triangle_iff hdet, Tco_line] at hacl
      specialize hacl i
      revert hacl
      simp
      rw [closed_side_to_co hdet (open_sub_closed _ hxT), zero_add,←neg_smul, det₂_mul_last,
          ←mul_assoc, ←neg_mul_eq_mul_neg, ←neg_mul_eq_neg_mul, neg_div, neg_neg_iff_pos, mul_assoc,  mul_div_assoc]
      apply mul_pos hapos
      rw [real_sign_mul, mul_assoc, mul_div_right_comm]
      exact mul_pos (real_sign_div_self hdet) (real_sign_mul_self (by rwa [Oside]))

lemma seg_sub_side {T : Triangle} {L : Segment} {x : ℝ²} {i : Fin 3} (hdet : det T ≠ 0)
    (hxL : x ∈ open_hull L) (hxT : x ∈ open_hull (Tside T i))
    (hInter : open_hull T ∩ closed_hull L = ∅)
    (hv : ∀ i, T i ∉ open_hull L) : closed_hull L ⊆ closed_hull (Tside T i) := by
  have hdir : det₂ (seg_vec (Tside T i)) (seg_vec L) = 0 := by
    by_contra hcontra
    have ⟨σ, hσ, ⟨δ, hδ, hain⟩, _⟩  := seg_inter_open hxT hdet hcontra
    have ⟨δ', hδ', hseg'⟩ := seg_dir_sub hxL
    rw [Set.eq_empty_iff_forall_not_mem] at hInter
    apply hInter (x + (min δ δ') • σ • seg_vec L)
    rw [@Set.mem_inter_iff]
    constructor
    · exact hain _ (lt_min hδ hδ') (min_le_left _ _)
    · rw [←mul_smul]
      refine open_sub_closed _ (hseg' (min δ δ' * σ) ?_)
      have hσabs : |σ| = 1 := by
        cases' (mem_insert.1 hσ) with ht ht
        · simp only [ht, abs_neg, abs_one]
        · simp at ht
          simp only [ht, abs_one]
      rw [abs_mul, hσabs, mul_one]
      refine Eq.trans_le (b := min δ δ') ?_ ?_
      · simp_all only [abs_eq_self, le_min_iff, and_self]
        constructor <;> linarith
      · exact min_le_right _ _
  intro y hy
  have hTyi : ∀ z, z ∈ closed_hull L →  Tco T z i = 0 := by
    intro z hz
    have ⟨b,hb⟩ := seg_vec_co (open_sub_closed _ hxL) hz
    rw [hb, Tco_line, Oside, hdir, mul_zero, zero_div,add_zero]
    exact closed_side_to_co hdet (open_sub_closed _ hxT)
  have hy₂ : y ∈ closed_hull T := by
    rw [closed_triangle_iff hdet]
    by_contra hc; push_neg at hc
    have ⟨j, hj⟩ := hc
    have hij : i ≠ j := by
      by_contra hij
      rw [←hij, hTyi y hy] at hj
      linarith
    have hxCoj : 0 < Tco T x j := by
      exact mem_open_side_other_co hdet hxT j hij.symm
    have hxCoij : 0 < Tco T x j - Tco T y j := by
      linarith
    let α : Fin 2 → ℝ := fun | 0 => ((- Tco T y j)/ (Tco T x j - Tco T y j)) | 1 => (Tco T x j/ (Tco T x j - Tco T y j))
    have hαSimp : α ∈ open_simplex 2 := by
      constructor
      · intro k
        fin_cases k <;>(
        · dsimp [α]
          field_simp
          linarith)
      · simp [α]
        field_simp
        ring
    let L' : Segment := fun | 0 => x | 1 => y
    let z := ∑ k, α k • L' k
    have hiz : Tco T z i = 0 := by
      simp_rw [z, Tco_linear hαSimp.2, Fin.sum_univ_two, L', hTyi x (open_sub_closed _ hxL), hTyi y hy]
      linarith
    have hjz : Tco T z j = 0 := by
      simp_rw [z, Tco_linear hαSimp.2, Fin.sum_univ_two, L', α]
      field_simp
      ring
    apply hv (last_index i j)
    rw [←(two_co_zero_imp_corner hdet hij hiz hjz)]
    apply open_segment_sub (L₁ := L')
    · intro k
      fin_cases k <;> simp [L']
      · exact (open_sub_closed _ hxL)
      · exact hy
    · simp [L']
      intro hcontra
      rw [←hcontra] at hj
      linarith [hj, hTyi x (open_sub_closed _ hxL)]
    · exact ⟨α,hαSimp,rfl⟩
  exact (mem_closed_side hdet hy₂ i).1 (hTyi y hy)



lemma segment_in_boundary_imp_in_side {T : Triangle} {L : Segment} (hdet : det T ≠ 0)
    (hL : closed_hull L ⊆ boundary T) : ∃ i, closed_hull L ⊆ closed_hull (Tside T i) := by
  have ⟨x,hx⟩ := open_seg_nonempty L
  have hxBoundary := hL (open_sub_closed _ hx)
  have hall : ∀ i, T i ∉ open_hull L := by

    sorry
  have ⟨i, hi⟩ := el_in_boundary_imp_side hdet hxBoundary ?_
  refine ⟨i,seg_sub_side hdet hx hi ?_ hall⟩
  · ext y; simp
    intro hyopen hyclosed
    refine (boundary_not_in_open (hL hyclosed)) hyopen
  · intro i hi
    specialize hall i
    rw [←hi] at hall
    exact hall hx


lemma closed_triangle_is_closed_dir {T : Triangle} (hdet : det T ≠ 0) {x y : ℝ²}
    (h : Set.Infinite {n : ℕ | x + (1 / (n : ℝ)) • y ∈ closed_hull T}) : x ∈ closed_hull T := by
  rw [closed_triangle_iff hdet]
  by_contra hContra; push_neg at hContra
  have ⟨i,hi⟩ := hContra
  have hB := Set.Infinite.not_bddAbove h
  rw [bddAbove_def] at hB
  push_neg at hB
  have hex : ∃ (n : ℕ), n > 0 ∧ (1/(n:ℝ)) * |(det₂ (Oside T i) y) / det T| < |Tco T x i| / 2 := by
    have ⟨n, hn⟩ := exists_nat_gt (max 0 ((|(det₂ (Oside T i) y) / det T|)/ (|Tco T x i| / 2)))
    use n
    rw [sup_lt_iff] at hn
    constructor
    · convert hn.1
      simp only [gt_iff_lt, Nat.cast_pos]
    · field_simp
      rw [div_lt_iff₀ hn.1, ←div_lt_iff₀' ?_]
      · exact hn.2
      · simp
        intro this
        rw [this] at hi
        exact (lt_self_iff_false 0).mp hi
  have ⟨n,hnpos,hn⟩ := hex
  have ⟨n',hn',hnn'⟩ := hB n
  dsimp at hn'
  rw [closed_triangle_iff] at hn'
  specialize hn' i
  rw [Tco_line] at hn'
  rw [←lt_self_iff_false (0:ℝ)]
  -- Annoying algebra
  calc
    0 ≤ Tco T x i + 1 / ↑n' * (det₂ (Oside T i) y / det T)    := by convert hn' using 2; ring
    _ ≤ Tco T x i + |1 / ↑n' * (det₂ (Oside T i) y / det T)|  := by gcongr; exact le_abs_self _
    _ = Tco T x i + (1 / ↑n') * |det₂ (Oside T i) y / det T|  := by
        rw [abs_mul]; congr; simp_all only [ne_eq,
        one_div, Set.mem_setOf_eq, gt_iff_lt, abs_eq_self, inv_nonneg, Nat.cast_nonneg]
    _ ≤ Tco T x i + (1 / ↑n) * |det₂ (Oside T i) y / det T|   := by gcongr
    _ < Tco T x i + |Tco T x i|/2                             := by gcongr
    _ = Tco T x i + (-Tco T x i)/2                            := by congr; exact abs_of_neg hi
    _ < 0                                                     := by linarith
  assumption


-- Basic lemmas about collinearity

lemma interior_left_trans {u v w t : ℝ²}
    (ht : t ∈ open_hull (to_segment u v)) (hv : v ∈ open_hull (to_segment u w)) :
    t ∈ open_hull (to_segment u w) := by
  sorry

lemma interior_collinear {u v w : ℝ²} (hv : v ∈ open_hull (to_segment u w)) : colin u v w := by
  sorry

lemma sub_collinear_left {u v w t : ℝ²} (hc : colin u v w) (ht : t ∈ open_hull (to_segment u v)) :
    colin u t v := by
  sorry

lemma sub_collinear_right {u v w t : ℝ²} (hc : colin u v w) (ht : t ∈ open_hull (to_segment u v)) :
    colin t v w := by
  sorry
