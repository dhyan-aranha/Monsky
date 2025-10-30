import Mathlib
import Mathlib.Tactic
import Monsky.simplex_basic
import Monsky.miscellaneous

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

-- Maybe useful but not used
-- lemma det₂_scalar {x y : ℝ²} (hy : y ≠ 0) (hdet : det₂ x y = 0) :
--     ∃ t : ℝ, x = t • y := by
--   rw [det₂, sub_eq_zero] at hdet
--   by_cases hy0 : y 0 = 0
--   · by_cases hy1 : y 1 = 0
--     · exfalso
--       apply hy (PiLp.ext ?_)
--       intro i
--       fin_cases i <;> assumption
--     · use x 1 / y 1
--       refine (PiLp.ext ?_)
--       intro i
--       fin_cases i
--       · field_simp
--         assumption
--       · field_simp
--   · use x 0 / y 0
--     refine (PiLp.ext ?_)
--     intro i
--     fin_cases i
--     · field_simp
--     · field_simp
--       exact hdet.symm





/- Segments -/

lemma open_segment_sub {L₁ L₂ : Segment} (hsub: ∀ i : Fin 2, L₁ i ∈ closed_hull L₂) (hL₁ : L₁ 0 ≠ L₁ 1) :
    open_hull L₁ ⊆ open_hull L₂ := by
  intro x ⟨α,hα,hx⟩
  refine (Set.mem_image (fun α ↦ ∑ i : Fin 2, α i • L₂ i) (open_simplex 2) x).mpr ?_
  have h1: ∃ α₁ ∈ closed_simplex 2, L₁ 0 = ∑ i : Fin 2, α₁ i • L₂ i := by
    rcases hsub 0 with ⟨β, hβ₁, β₁₀⟩
    exact Filter.frequently_principal.mp fun a => a hβ₁ (id (Eq.symm β₁₀))
  have h2: ∃ α₂ ∈ closed_simplex 2, L₁ 1 = ∑ i : Fin 2, α₂ i • L₂ i := by
    rcases hsub 1 with ⟨β, hβ₁, β₁₀⟩
    exact Filter.frequently_principal.mp fun a => a hβ₁ (id (Eq.symm β₁₀))
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
      exact hL₁ hL₁₀
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
  rw [@mem_coe, @mem_image]
  let f : Fin 2 → Fin 2 := fun | 0 => 1 | 1 => 0
  constructor
  · intro hx
    have ⟨α,hα,hαx⟩ := boundary_in_closed hx
    have α_non_zero : ∃ i, α i = 0 := by
      by_contra hcontra; push_neg at hcontra
      apply boundary_not_in_open hx
      exact ⟨α,⟨fun i ↦ lt_of_le_of_ne (hα.1 i) (hcontra i).symm,hα.2⟩ ,hαx⟩
    have ⟨i,hi⟩ := α_non_zero
    have hf : α (f i) = 1 := by
      rw [←hα.2]
      fin_cases i <;> simp_all [f]
    use f i, mem_univ (f i)
    simp only [←hαx, Fin.sum_univ_two]
    fin_cases i <;> simp_all [f]
  · intro ⟨i, _, hi⟩
    rw [boundary, @Set.mem_diff]
    constructor
    · rw [← hi]
      exact corner_in_closed_hull
    · intro ⟨α, hα, hxα⟩
      have h : (α (f i)) • L i = (α (f i)) • L (f i) := by
        calc
          (α (f i)) • L i = (1 - α i) • L i     := by
            congr;
            rw [(simplex_open_sub_fin2 hα (f i))];
            fin_cases i <;> simp [f]
          (1 - α i) • L i = L i - α i • L i     := by module
          _               =  x  - α i • L i     := by rw [hi]
          _               =  α (f i) • L (f i)  := by
            rw [←hxα]
            fin_cases i <;> simp [f]
      apply hL
      have this := smul_cancel (Ne.symm (ne_of_lt (hα.1 (f i)))) h
      fin_cases i <;> (simp [f] at this; rw [this])

lemma boundary_seg' {L : Segment} (hL: L 0 ≠ L 1) : ∀ (i : Fin 2), L i ∈ boundary L := by
  intro i
  rw [boundary_seg]
  simp only [coe_image, coe_univ, Set.image_univ, Set.mem_range, exists_apply_eq_apply]
  apply hL

lemma boundary_seg_set {L :Segment} (hL : L 0 ≠ L 1) : boundary L = {L 0, L 1} := by
  rw [boundary_seg hL]
  ext x
  constructor
  · intro hx
    simp at hx
    rcases hx with ⟨i, _, hi⟩
    fin_cases i
    simp only [Fin.isValue, Fin.zero_eta, Set.mem_insert_iff, Set.mem_singleton_iff, true_or]
    simp only [Fin.isValue, Fin.mk_one, Set.mem_insert_iff, Set.mem_singleton_iff, or_true]
  · simp only [Fin.isValue, Set.mem_insert_iff, Set.mem_singleton_iff, coe_image, coe_univ,
    Set.image_univ, Set.mem_range]
    intro hx
    rcases hx with ⟨i, hi⟩
    use (0 : Fin 2)
    use (1 : Fin 2)
    tauto

lemma boundary_seg_nonempty {L :Segment} {x : ℝ²} (hx : x ∈ boundary L)
    : L 0 ≠ L 1 := by
  intro hc
  have hi : ∀ i, L i = L 0 := by
    intro i
    fin_cases i <;> simp_all
  rw [←Set.mem_empty_iff_false x]
  convert hx
  convert (boundary_constant (P := L 0)).symm using 2
  ext i
  rw [hi i]



lemma sign_seg_line (L : Segment) (x y : ℝ²) (a : ℝ) :
    sign_seg L (x + a • y) = (sign_seg L x) + a * (det₂ (seg_vec L) y) := by
  simp [sign_seg, det₂, det, seg_vec]; ring

lemma seg_vec_zero_iff (L : Segment) : seg_vec L = 0 ↔ L 0 = L 1 := by
  rw [seg_vec, sub_eq_zero]
  exact eq_comm

lemma seg_vec_nonzero_iff (L : Segment) : seg_vec L ≠ 0 ↔ L 0 ≠ L 1 :=
    not_congr (seg_vec_zero_iff L)

lemma closed_segment_interval_im {L : Segment} :
    closed_hull L = (fun a ↦ L 0 + a • seg_vec L) '' (Set.Icc 0 1 : Set ℝ)  := by
  ext x
  constructor
  · intro ⟨α, hα, hαx⟩
    use 1 - α 0
    constructor
    · simp [simplex_co_leq_1 hα 0, hα.1 0]
    · simp [←hαx, simplex_closed_sub_fin2 hα 1, seg_vec]
      module
  · intro ⟨a, ha, hax⟩
    use (real_to_fin_2 (1 - a)), real_to_fin_2_closed (by linarith [ha.2]) (by linarith [ha.1])
    simp [←hax, real_to_fin_2, seg_vec]
    module

-- Same proof essentially.
lemma open_segment_interval_im {L : Segment} :
    open_hull L = (fun a ↦ L 0 + a • seg_vec L) '' (Set.Ioo 0 1 : Set ℝ)  := by
  ext x
  constructor
  · intro ⟨α, hα, hαx⟩
    use 1 - α 0
    constructor
    · constructor
      · linarith [simplex_co_leq_1_open Nat.one_lt_two hα 0]
      · linarith [hα.1 0]
    · simp [←hαx, simplex_open_sub_fin2 hα 1, seg_vec]
      module
  · intro ⟨a, ha, hax⟩
    use (real_to_fin_2 (1 - a)), real_to_fin_2_open (by linarith [ha.2]) (by linarith [ha.1])
    simp [←hax, real_to_fin_2, seg_vec]
    module


lemma seg_vec_zero_closed_hull {L : Segment} (hL : seg_vec L = 0) :
    closed_hull L = {L 0} := by
  rw [closed_segment_interval_im, hL]
  simp

lemma seg_vec_zero_open_hull {L : Segment} (hL : seg_vec L = 0) :
    open_hull L = {L 0} := by
  rw [open_segment_interval_im, hL]
  simp


lemma seg_dir_sub {L : Segment} {x : ℝ²} (hxL : x ∈ open_hull L) :
    ∃ δ > 0, ∀ (a : ℝ), |a| ≤ δ → x + a • seg_vec L ∈ open_hull L := by
  rw [open_segment_interval_im] at *
  have ⟨a, ha, hax⟩ := hxL
  use (min ((a)/2) ((1- a)/2))
  constructor
  · simp
    exact ha
  · intro b hb
    rw [←hax]
    use a + b
    constructor
    · rw [@Set.add_mem_Ioo_iff_right, zero_sub, Set.mem_Ioo]
      rw [@le_min_iff, @abs_le, @abs_le] at hb
      constructor
      · refine gt_of_ge_of_gt hb.1.1 ?_
        linarith [ha.1]
      · refine lt_of_le_of_lt hb.2.2 ?_
        linarith [ha.2]
    · module


lemma seg_vec_co {L : Segment} {x y : ℝ²} (hx : x ∈ closed_hull L) (hy : y ∈ closed_hull L)
  : ∃ a : ℝ, y = x + a • seg_vec L := by
  rw [closed_segment_interval_im] at hx hy
  have ⟨a₁, _, hx⟩ := hx
  have ⟨a₂, _, hy⟩ := hy
  use a₂ - a₁
  simp [←hx, ←hy, smul_sub, sub_smul]


lemma open_seg_nonempty (L : Segment) : ∃ x, x ∈ open_hull L :=
  open_pol_nonempty Nat.zero_lt_two L


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
lemma segment_rfl {L : Segment}
    : to_segment (L 0) (L 1) = L :=
  List.ofFn_inj.mp rfl

@[simp]
lemma reverse_segment_to_segment {u v : ℝ²}
  : reverse_segment (to_segment u v) = to_segment v u := rfl

@[simp]
lemma reverse_segment_involution {L : Segment}
    : reverse_segment (reverse_segment L) = L :=
  List.ofFn_inj.mp rfl

lemma reverse_segment_bijective : Function.Bijective reverse_segment :=
  Function.Involutive.bijective (Function.involutive_iff_iter_2_eq_id.mpr (by ext _; simp))


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
  exact Set.Subset.antisymm (haux _) (haux _)


lemma reverse_segment_boundary {L : Segment}
    : boundary (reverse_segment L) = boundary L := by
  simp [boundary, reverse_segment_open_hull, reverse_segment_closed_hull]


lemma segment_triv {L : Segment} : L 0 = L 1 ↔ ∃ x, closed_hull L = {x} := by
  constructor
  · intro h
    exact ⟨L 0, by
      convert closed_hull_constant (n := 2) (P := L 0) (by norm_num) using 2
      ext i j;
      fin_cases i <;> simp_all
    ⟩
  · intro ⟨x, hx⟩
    have h₁₂ : L 0  ∈ ({x} : Set ℝ²) ∧ L 1  ∈ ({x} : Set ℝ²) := by
      constructor <;> (rw [←hx]; exact corner_in_closed_hull )
    rw [h₁₂.1, h₁₂.2]

lemma segment_triv' {L : Segment} : L 0 = L 1 ↔ closed_hull L = {L 0} := by
  rw [segment_triv]
  constructor
  · intro ⟨x, hx⟩
    rw [hx]
    suffices hL : L 0 ∈ ({x} : Set ℝ²)
    · simp [hL.symm]
    · rw [←hx]
      exact corner_in_closed_hull
  · exact fun h ↦ ⟨L 0, h⟩


lemma seg_nontriv_sub {L₁ L₂ : Segment} (h : closed_hull L₁ ⊆ closed_hull L₂) (hneq : L₁ 0 ≠ L₁ 1)
    : L₂ 0 ≠ L₂ 1 := by
  intro hContra
  rw [segment_triv'.1 hContra, Set.subset_singleton_iff] at h
  apply hneq
  rw [h (L₁ 0) corner_in_closed_hull, h (L₁ 1) corner_in_closed_hull]





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
        · use 1, Real.zero_lt_one -- Junk value
          intro a ⟨hapos, _⟩
          rw [hij, closed_side_to_co hdet (open_sub_closed _ hxT), zero_add, mul_div_assoc]
          apply mul_pos hapos
          rw [det₂_mul_last, real_sign_mul, mul_assoc, mul_div_right_comm]
          exact mul_pos (real_sign_div_self hdet) (real_sign_mul_self hdet₂)
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
      exact mul_pos (real_sign_div_self hdet) (real_sign_mul_self hdet₂)

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
      intro hij
      rw [←hij, hTyi y hy] at hj
      exact (lt_self_iff_false 0).mp hj
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
  by_cases hLTriv : L 0 = L 1
  · have hconstant : closed_hull L = {L 0} := by
      convert closed_hull_constant (Nat.zero_ne_add_one 1).symm using 2
      ext i; fin_cases i <;> simp [hLTriv]
    simp_rw [hconstant, Set.singleton_subset_iff] at *
    exact el_boundary_imp_side hdet hL
  · have ⟨x,hx⟩ := open_seg_nonempty L
    have hxBoundary := hL (open_sub_closed _ hx)
    have hall : ∀ i, T i ∉ open_hull L := by
      intro i hi
      have ⟨δ, hδ, hδa⟩ := seg_dir_sub hi
      have haux : ∀ j, ∀ a, j ≠ i → |a| ≤ δ → a * det₂ (seg_vec (Tside T j)) (seg_vec L) / det T ≥ 0 := by
        intro j a hji ha'
        have ht := (closed_triangle_iff hdet).1 (boundary_sub_closed _ (hL (open_sub_closed _ (hδa a ha')))) j
        rwa [@Tco_line, Tco_basis_off_diag hji.symm, zero_add] at ht
      have haux2 : ∀ j, j ≠ i → det₂ (seg_vec (Tside T j)) (seg_vec L) = 0 := by
        intro j hji
        have h₁ := haux j δ  hji ?_
        have h₂ := haux j (-δ) hji ?_
        rw [←(div_left_inj' hdet), zero_div]
        rw [mul_div_assoc] at h₁ h₂
        linarith [nonneg_of_mul_nonneg_right h₁ hδ, nonpos_of_mul_nonneg_right h₂ (neg_neg_iff_pos.mpr hδ)]
        all_goals simp only [abs_neg, abs_of_pos hδ, le_refl]
      have hcontra :  T i = T i + δ • seg_vec L := by
        let j : Fin 3 := ⟨(i + 1)%3, by omega⟩
        let k : Fin 3 := ⟨(i + 2)%3, by omega⟩
        have hij : i ≠ j := by fin_cases i <;> simp [j]
        have hik : i ≠ k := by fin_cases i <;> simp [k]
        have hjk : j ≠ k := by fin_cases i <;> simp [j, k]
        convert (two_co_zero_imp_corner hdet hjk ?_ ?_).symm
        · fin_cases i <;> simp [j,k,last_index]
        · rw [Tco_line, Tco_basis_off_diag hij, Oside, haux2 j hij.symm, zero_add, mul_zero, zero_div]
        · rw [Tco_line, Tco_basis_off_diag hik, Oside, haux2 k hik.symm, zero_add, mul_zero, zero_div]
      apply hLTriv
      rw [←seg_vec_zero_iff]
      rw [@self_eq_add_right, smul_eq_zero] at hcontra
      cases hcontra
      · linarith
      · assumption
    have ⟨i, hi⟩ := el_in_boundary_imp_side hdet hxBoundary ?_
    refine ⟨i,seg_sub_side hdet hx hi ?_ hall⟩
    · ext y; simp
      intro hyopen hyclosed
      refine (boundary_not_in_open (hL hyclosed)) hyopen
    · exact fun i => ne_of_mem_of_not_mem hx (hall i)


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
      exact Iff.symm Nat.cast_pos'
    · field_simp
      rw [div_lt_iff₀ hn.1, ←div_lt_iff₀' ?_]
      · exact hn.2
      · simp [ne_of_lt hi]
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



lemma colin_reverse {u v w : ℝ²} (h : colin u v w) : colin w v u := by
  have ⟨h₁,h₂⟩ := h
  exact ⟨h₁.symm, by rwa [←reverse_segment_open_hull, reverse_segment_to_segment]⟩


lemma colin_decomp_closed {u v w :ℝ²} (h :colin u v w ) : closed_hull (to_segment u w)
  = closed_hull (to_segment u v) ∪ closed_hull (to_segment v w) := by
  have hv: v ∈ closed_hull (to_segment u w) := by apply open_sub_closed _ h.2
  have hu: u ∈ closed_hull (to_segment u w) := by apply corner_in_closed_hull (i := 0) (P := to_segment u w)
  ext z
  constructor
  intro hx
  simp [closed_segment_interval_im, to_segment, seg_vec] at *
  rcases hx with ⟨β, hβ, hβz⟩
  rcases hv with ⟨α, hα, hαv⟩
  by_cases t : β ≤ α
  · left
    by_cases hα0 : α = 0
    · use 0
      rw [hα0] at hαv
      simp only [zero_smul, add_zero] at hαv
      have t' : β = 0 := by linarith
      rw [t'] at hβz
      simp only [zero_smul, add_zero] at hβz
      simp only [le_refl, zero_le_one, and_self, hβz, zero_smul, add_zero]
    by_cases hβ0 : β = 0
    · use 0
      rw [hβ0] at hβz
      simp only [zero_smul, add_zero] at hβz
      simp only [zero_smul, add_zero, zero_le_one, and_self, hβz, le_refl]
    · use β/α
      have hα0': α ≠ 0 := hα0
      have hαpos : 0 < α := by
        apply lt_of_le_of_ne
        · exact hα.1
        · exact hα0'.symm
      have hβpos : 0 < β := by
        apply lt_of_le_of_ne
        · exact hβ.1
        · exact Ne.symm hβ0
      constructor
      · constructor
        · apply div_nonneg
          · exact hβ.1
          · exact hα.1
        · rw [div_le_one]
          · apply t
          · exact hαpos
      rw [← hαv]
      simp only [add_sub_cancel_left]
      have n: u + (β / α) • α • (w - u) = u + β • (w - u) := by
        rw [←mul_smul]
        field_simp
      rw [n]
      apply hβz
  · right
    have t': α < β := by rw [not_le] at t; exact t
    by_cases hβ0 : β = 0
    · by_contra
      have hα0' : 0 ≤ α := by linarith
      rw [hβ0] at t'
      linarith
    have hαnot1: α ≠ 1 := by
      by_contra hα1
      have hβcont: 1 < β :=by
        rw [hα1] at t'
        linarith
      have hβcont' : β ≤ 1 := by
        exact hβ.2
      linarith
    · use (β - α) / (1 - α)
      constructor
      · constructor
        · apply div_nonneg
          · linarith
          · linarith
        · rw [div_le_one]
          · linarith
          · linarith
      rw [← hβz, ←hαv]
      have hβ' : β = (β - β • α)/(1 - α ) := by
        field_simp
        have hβ'' : (β - β * α) = β * (1 - α) := by
          ring_nf
        rw [hβ'', mul_comm]
        have hβ''': (1 - α) * β / (1 - α) = ((1-α)/ (1-α)) * β := by
          rw [mul_div_assoc]
          field_simp
        have hβ'''': (1 - α) / (1 - α) = 1 := by
          rw [div_self]
          linarith
        rw [hβ''', hβ'''', one_mul]
      let q := (β - α) / (1 - α)
      have hq : (β - α) / (1 - α) = q := rfl
      rw[hq]
      rw [smul_sub, smul_sub, add_assoc, ← add_sub_assoc, ← add_sub_assoc, ← add_sub_assoc]
      have hq' : q • (u + α • w - α • u) = q•u + q•α•w - q•α•u := by
        rw [add_sub_assoc, smul_add, smul_sub, add_sub_assoc]
      rw [hq']
      have hr''' : α + q - q * α = β := by
        rw [← hq]
        have hra : α + (β - α) / (1 - α) - (β - α) / (1 - α) * α = (1-α)/(1-α) * α + (β - α) / (1 - α) - (β - α) / (1 - α) * α := by
          rw [div_self]
          linarith
          by_contra hcontra
          have  hcontra' : α = 1 := by
              linarith
          linarith
        rw [hra]
        ring_nf
        have hra' : -(α * (1 - α)⁻¹ * β) + (1 - α)⁻¹ * β = (β - β • α) / (1 - α) := by
          field_simp
          ring_nf
        rw [hra']
        apply hβ'.symm
      simp [smul_sub, ← hr''']
      module
  intro hz
  by_cases t: z ∈ closed_hull (to_segment u v)
  have hu': u ∈ closed_hull (to_segment u w):=  by
    · apply corner_in_closed_hull (i := 0) (P := to_segment u w)
  have hv': v ∈ closed_hull (to_segment u w):=  by
    · apply open_sub_closed _ h.2
  have huvcont: closed_hull (to_segment u v) ⊆ closed_hull (to_segment u w) := by
    apply closed_hull_convex
    intro i
    fin_cases i
    · exact hu'
    · exact hv'
  exact huvcont t
  have hzcl:  z ∈ closed_hull (to_segment v w) := by
    tauto_set
  have hv'': v ∈ closed_hull (to_segment u w):=  by
    · apply open_sub_closed _ h.2
  have hw : w ∈ closed_hull (to_segment u w):=  by
    · apply corner_in_closed_hull (i := 1) (P := to_segment u w)
  have hvwcont: closed_hull (to_segment v w) ⊆ closed_hull (to_segment u w) := by
    apply closed_hull_convex
    intro i
    fin_cases i
    · exact hv''
    · exact hw
  tauto_set

  lemma middle_not_boundary_colin {u v w : ℝ²} (hcolin: colin u v w) : (u ≠ v) ∧ (v ≠ w) := by
  have ht : ∀ {u' v' w' : ℝ²}, colin u' v' w' → u' ≠ v' := by
    intro u _ w ⟨h₁, h₂⟩ huv
    refine boundary_not_in_open ?_ h₂
    convert boundary_seg' (L := to_segment u w) h₁ 0
    rw [huv, to_segment]
  exact ⟨ht hcolin, (ht (colin_reverse hcolin)).symm⟩

lemma left_open_hull_in_colin {u v w : ℝ²} {h: colin u v w} :
  open_hull (to_segment u v) ⊆ open_hull (to_segment u w) := by
  apply open_segment_sub'
  have this := colin_decomp_closed h
  tauto_set
  rw [to_segment, to_segment]; exact (middle_not_boundary_colin h).1

lemma right_open_hull_in_colin {u v w : ℝ²} {h : colin u v w}
  : open_hull (to_segment v w) ⊆ open_hull (to_segment u w) := by
  apply open_segment_sub'
  have this := colin_decomp_closed h
  tauto_set
  rw [to_segment, to_segment]; exact (middle_not_boundary_colin h).2


lemma interior_left_trans {u v w t : ℝ²}
(ht : t ∈ open_hull (to_segment u v)) (hv : v ∈ open_hull (to_segment u w)) :
t ∈ open_hull (to_segment u w) := by
    by_cases huv : u = v
    · have hopen : open_hull (to_segment v v) = {v} := open_hull_constant (by norm_num) (P := v)
      rw [huv, hopen, Set.mem_singleton_iff] at ht
      exact Set.mem_of_eq_of_mem ht hv
    · refine (open_segment_sub' ?_ huv) ht
      apply closed_hull_convex
      intro i
      fin_cases i
      · exact corner_in_closed_hull (i := 0) (P := to_segment u w)
      · exact open_sub_closed _ hv

--This definition is meant to help with showing that if u v w, and v w x are colinear, then so are u w x and u v x. In particular this definition gives the simplex that will be used to show that both v w are in the open hull of u x
noncomputable def make_new_two_simplex (a b : Fin 2 → ℝ): (Fin 2 → ℝ ):= fun | 0 => a 0/(1 - a 1 * b 0) | 1 => a 1 * b 1 /(1 - a 1 *  b 0)

--This lemma shows that the above defined simplex is indeed a two simplex
lemma make_new_two_simplex_lem (a b : Fin 2 → ℝ)(ha_simplex : a ∈ open_simplex 2)(hb_simplex : b ∈ open_simplex 2): make_new_two_simplex a b ∈ open_simplex 2 := by
  have hhelp :=  sub_pos.mpr (mul_lt_one_of_nonneg_of_lt_one_left (le_of_lt (ha_simplex.1 1)) (simplex_co_leq_1_open  (by norm_num) ha_simplex 1) (le_of_lt (simplex_co_leq_1_open (by norm_num) hb_simplex 0)))
  constructor
  · intro i ; fin_cases i
    exact div_pos (ha_simplex.1 0)  hhelp
    exact div_pos (mul_pos (ha_simplex.1 1) (hb_simplex.1 1))  hhelp
  · unfold make_new_two_simplex
    simp
    have h : (a 0 + a 1 *b 1) / (1 - a 1 * b 0) = 1 --This h is probably not necessary
    apply (div_eq_one_iff_eq (Ne.symm (ne_of_lt hhelp))).mpr
    rw[simplex_open_sub_fin2 ha_simplex 1 ,simplex_open_sub_fin2 hb_simplex 1]
    linarith
    nth_rewrite 3[← h]
    exact div_add_div_same (a 0) (a 1 * b 1) (1 - a 1 * b 0)

--This lemma shows that indeed v is in the open hull, using the above defined simplex. It effectively also shows the same for w, (use two_colin_in_open_hull (colin_reverse h₂) (colin_reverse h₁), with  rw[← reverse_segment_to_segment])
lemma two_colin_in_open_hull {u v w x : ℝ²} (h₁ : colin u v w) (h₂ : colin v w x) : v ∈ open_hull (to_segment u x) := by
  rcases h₁ with ⟨h_u_neq_w, ⟨ a, ha_simplex, havuw⟩  ⟩
  rcases h₂ with ⟨h_v_neq_x, ⟨ b, hb_simplex, hbwvx⟩  ⟩
  simp[ to_segment] at *
  use make_new_two_simplex a b
  constructor
  · exact make_new_two_simplex_lem a b ha_simplex hb_simplex
  · simp[to_segment, make_new_two_simplex]
    rw[← hbwvx] at havuw

    have h2 : a 0 • u + (a 1 * b 0) • v + (a 1 * b 1) • x =  v
    repeat rw[mul_smul]
    simp at *
    rwa[add_assoc]

    have h1: a 0 • u + (a 1 * b 1) • x = (1 - (a 1 * b 0)) • v
    rw[sub_smul, one_smul]
    apply eq_sub_of_add_eq
    nth_rewrite 2[← h2]
    module
    have h: (1 - a 1 * b 0) > 0 := sub_pos.mpr (mul_lt_one_of_nonneg_of_lt_one_left (le_of_lt (ha_simplex.1 1)) (simplex_co_leq_1_open  (by norm_num) ha_simplex 1) (le_of_lt (simplex_co_leq_1_open (by norm_num) hb_simplex 0)))
    rw[← inv_smul_eq_iff₀ (Ne.symm (ne_of_lt h))] at h1
    rw[← h1]
    simp
    module

--These two lemmas show that if u v w and v w x then u v x and u w x are also colinear, starting with the latter
lemma colin_trans_right {u v w x : ℝ²} (h₁ : colin u v w) (h₂ : colin v w x) : colin u w x := by
  have hw :=  two_colin_in_open_hull (colin_reverse h₂) (colin_reverse h₁)
  rw[← reverse_segment_to_segment , reverse_segment_open_hull] at hw
  constructor
  · by_contra hcontra
    rw [hcontra] at hw
    have hux' : open_hull (to_segment x x) = {x} := by
       apply open_hull_constant
       linarith
    rw [hux', Set.mem_singleton_iff] at hw
    have hwnx : w ≠ x := by
      apply (middle_not_boundary_colin h₂).2
    contradiction
  · exact hw

lemma colin_trans_left {u v w x : ℝ²} (h₁ : colin u v w) (h₂ : colin v w x) : colin u v x := by
  have hv := two_colin_in_open_hull h₁ h₂
  constructor
  · by_contra hcontra
    rw [hcontra] at hv
    have hvx' : open_hull (to_segment x x) = {x} := by
       apply open_hull_constant
       linarith
    rw [hvx', Set.mem_singleton_iff] at hv
    have hvnx : v ≠ x := by
        apply h₂.1
    contradiction
  · exact hv

lemma sub_collinear_left {u v w t : ℝ²} (hc : colin u v w) (ht : t ∈ open_hull (to_segment u v)) :
    colin u t v := ⟨(middle_not_boundary_colin hc).1,ht⟩

lemma sub_collinear_right {u v w t : ℝ²} (hc : colin u v w) (ht : t ∈ open_hull (to_segment u v)) :
    colin t v w := by
  refine ⟨(middle_not_boundary_colin ⟨hc.1, (interior_left_trans ht hc.2)⟩).2, ?_⟩
  have hv := hc.2
  simp [open_segment_interval_im, to_segment, seg_vec] at *
  have ⟨a₁, ha₁, ht⟩ := ht
  have ⟨a₂, ha₂, hv⟩ := hv
  have hnum : 0 < (1 - a₁ * a₂) := by
    rw [sub_pos]
    have htemp : a₂ < 1 + (1 - a₁) * a₂ :=
      lt_add_of_lt_of_pos ha₂.2 (mul_pos (by linarith) ha₂.1)
    linarith
  refine ⟨((1 - a₁) * a₂) / (1 - a₁ * a₂), ⟨?_, ?_⟩ , ?_⟩
  · field_simp
    exact mul_pos (by linarith) (by linarith)
  · rw [div_lt_iff₀ hnum]
    linarith
  · rw [←ht, ←hv]
    ext i
    field_simp
    ring

-- A slightly stronger version.
lemma sub_collinear_right' {u v w t : ℝ²} (hc : colin u v w) (ht : t ∈ closed_hull (to_segment u v))
    (htv : t ≠ v) : colin t v w := by
  by_cases ht_open : t ∈ open_hull (to_segment u v)
  · exact sub_collinear_right hc ht_open
  · have ht_boundary : t ∈ boundary (to_segment u v) := Set.mem_diff_of_mem ht ht_open
    rw [boundary_seg (by convert (middle_not_boundary_colin hc).1)] at ht_boundary
    simp only [coe_image, coe_univ, Set.image_univ, Set.mem_range] at ht_boundary
    have ⟨i, hi⟩ := ht_boundary
    fin_cases i
    · rw [←hi]
      exact hc
    · rw [←hi] at htv
      tauto


lemma closed_in_clopen_right {v z w : ℝ²} (hvw : v ≠ w) (hz: z ∈ closed_hull (to_segment v w) \ {v}) :
closed_hull (to_segment z w) ⊆ closed_hull (to_segment v w) \ {v} := by
by_cases hzw : z = w
· rw [hzw]
  have hzwconst : closed_hull (to_segment w w) = {w} := by
    apply closed_hull_constant
    linarith
  rw [hzwconst]
  simp only [Set.singleton_subset_iff, Set.mem_diff, Set.mem_singleton_iff]
  constructor
  · tauto_set
  · apply hvw.symm
· have hzcl : z ∈ closed_hull (to_segment v w) := by
   tauto_set
  have hzwcl : closed_hull (to_segment z w) ⊆ closed_hull (to_segment v w) := by
   apply closed_hull_convex
   intro i
   fin_cases i
   · simp
     exact hzcl
   · apply corner_in_closed_hull (i := 1) (P := to_segment v w)
  have hopen : open_hull (to_segment z w) ⊆ open_hull (to_segment v w) := by
   apply open_segment_sub' hzwcl
   rw[to_segment, to_segment]
   apply hzw
  have hvwboundary : boundary (to_segment v w) = {v, w} := by
    apply boundary_seg_set
    rw [to_segment, to_segment]
    apply hvw
  have hw : w ∈ closed_hull (to_segment v w) \ {v} := by
   rw [← boundary_union_open_closed]
   rw [hvwboundary]
   simp only [Set.mem_diff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, or_true,
     true_or, true_and]
   apply hvw.symm
  have hzwboundary : boundary (to_segment z w) = {z, w} := by
   apply boundary_seg_set
   rw [to_segment, to_segment]
   apply hzw
  rw [← boundary_union_open_closed]
  rw [hzwboundary]
  simp
  constructor
  have hzhw : {z,w} ⊆ closed_hull (to_segment v w) \ {v} := by
   intro x hx
   by_cases hxz : x = z
   rw [hxz]
   exact hz
   have hxw : x = w := by
    simp_all only [ne_eq, Set.mem_diff, Set.mem_singleton_iff, true_and, Set.mem_insert_iff,
      false_or]
   rw [hxw]
   rw [← boundary_union_open_closed]
   rw [hvwboundary]
   simp only [Set.mem_diff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, or_true,
     true_or, true_and, ne_eq]
   apply hvw.symm
  apply hzhw
  have hzopen : open_hull (to_segment  v w) ⊆ closed_hull (to_segment v w) \ {v} := by
    rw [← open_closed_hull_minus_boundary]
    tauto_set
  tauto_set


lemma corrollary_closed_in_clopen_right {v z w : ℝ²}
  (hclop: closed_hull (to_segment z w) ⊆ closed_hull (to_segment v w) \ {v} ): v ∉ closed_hull (to_segment z w) := by
  by_contra h
  have this := hclop h
  simp at this


lemma middle_intersection_empty {u v w : ℝ²} {h : colin u v w} :
 closed_hull (to_segment u v) ∩ (closed_hull (to_segment v w) \ {v}) = ∅ := by
by_contra hcontra
have hmid : Set.Nonempty (closed_hull (to_segment u v) ∩ (closed_hull (to_segment v w) \ {v})) := by
  exact Set.nonempty_iff_ne_empty.mpr hcontra
have hmid' : ∃ z, z ∈ closed_hull (to_segment u v) ∩ (closed_hull (to_segment v w) \ {v}) := by
  exact Set.nonempty_def.mp hmid
rcases hmid' with ⟨z, hz⟩
have hzv : z ≠ v := by
  intro hzv
  rw [hzv] at hz
  have hv : v ∉ closed_hull (to_segment u v) := by
    rw [closed_segment_interval_im, to_segment, seg_vec] at hz
    tauto_set
  have hv' : v ∈ closed_hull (to_segment u v) := by
    apply corner_in_closed_hull (i := 1) (P := to_segment u v)
  contradiction
have hzuv : z ∈ closed_hull (to_segment u v) := by
 tauto_set
have hzvwv : z ∈ closed_hull (to_segment v w) \ {v} := by
  tauto_set
have hv1 : v ∈ closed_hull (to_segment z w) := by
  have hv1' : colin z v w := by
    exact sub_collinear_right' h hzuv hzv
  apply open_sub_closed _
  apply hv1'.2
have hg : closed_hull (to_segment z w) ⊆ closed_hull (to_segment v w) \ {v} := by
  apply closed_in_clopen_right
  exact (middle_not_boundary_colin h).2
  apply hzvwv
have hg' : v ∉ closed_hull (to_segment z w) := by
  exact corrollary_closed_in_clopen_right hg
contradiction


lemma colin_intersection_open_hulls_empty {u v w :ℝ²}{h : colin u v w} :
open_hull (to_segment u v) ∩ open_hull (to_segment v w) = ∅ := by

have huv : open_hull (to_segment u v) ⊆ closed_hull (to_segment u v) := by
  apply open_sub_closed
have hvw : open_hull (to_segment v w) ⊆  (closed_hull (to_segment v w) \ {v}) := by
  intro x hx
  have hvwclosed : x ∈ closed_hull (to_segment v w) := by
    apply open_sub_closed
    apply hx
  have hnx: x ≠ v := by
    rw [← open_closed_hull_minus_boundary] at hx
    rw [boundary_seg_set] at hx
    tauto_set
    exact (middle_not_boundary_colin h).2
  tauto_set
have hclopen : closed_hull (to_segment u v) ∩ (closed_hull (to_segment v w) \ {v}) = ∅ := by
  apply middle_intersection_empty
  apply h
tauto_set







lemma clopen_left {u v w : ℝ²}{h: colin u v w} : closed_hull (to_segment u w) \ closed_hull (to_segment u v)
= closed_hull (to_segment v w) \ {v} := by
  ext z
  constructor
  intro hz
  have clovw : z ∈ closed_hull (to_segment v w) := by
    rw [colin_decomp_closed h] at hz
    tauto_set
  have hzv : z ≠ v := by
    intro hzv
    rw [hzv] at hz
    have hv : v ∉ closed_hull (to_segment u v) := by
      rw [closed_segment_interval_im, to_segment, seg_vec] at hz
      tauto_set
    have hv' : v ∈ closed_hull (to_segment u v) := by
      apply corner_in_closed_hull (i := 1) (P := to_segment u v)
    tauto_set
  tauto_set
  intro hz
  have hzuw : z ∈ closed_hull (to_segment u w) := by
    rw [colin_decomp_closed h]
    tauto_set
  have hzuv :  z ∉ closed_hull (to_segment u v) := by
    by_contra hcontra
    have hmid : closed_hull (to_segment u v) ∩ (closed_hull (to_segment v w) \ {v}) = ∅ := by
      apply middle_intersection_empty
      apply h
    have hzmid: z ∈ closed_hull (to_segment u v) ∩ (closed_hull (to_segment v w) \ {v}) := by
      tauto_set
    have hempty : Set.singleton z = ∅ := by
      rw [← hmid]
      rw [← Set.singleton_subset_iff] at hzmid
      tauto_set
    have hnempty : Set.singleton z ≠ ∅ := by
      intro hcontra
      exact Set.not_mem_empty z (Set.mem_singleton_iff.mp hcontra ▸ Set.mem_singleton z)
    contradiction
  tauto_set




lemma sub_collinear_right_symm' {u v w t : ℝ²} (hc : colin u v w) (ht : t ∈ closed_hull (to_segment v w))
    (htv : t ≠ v) : colin u v t := by
  apply colin_reverse
  refine sub_collinear_right' (hc := colin_reverse hc) ?_ htv
  convert ht using 1;
  convert reverse_segment_closed_hull
  simp only [reverse_segment_to_segment]



lemma colin_sub_aux {u v w x : ℝ²} {L : Segment} (hc : colin u v w)
    (hLsub : closed_hull L ⊆ closed_hull (to_segment u w)) (hv : v ∉ open_hull L) (hxL : x ∈ open_hull L)
    (hx : x ∈ closed_hull (to_segment u v)) : closed_hull L ⊆ closed_hull (to_segment u v) := by
  by_cases hL01 : L 0 = L 1
  · rw [←Set.singleton_subset_iff] at hx
    convert hx
    have hxcL : x ∈ closed_hull L := by
      apply open_sub_closed _ hxL
    have hconstant : closed_hull L = {L 0} := by
      convert closed_hull_constant (Nat.zero_ne_add_one 1).symm using 2
      ext i; fin_cases i <;> simp [hL01]
    rw [hconstant] at hxcL
    rw [hconstant]
    rw [← Set.singleton_subset_iff, Set.singleton_subset_singleton] at hxcL
    rw [hxcL]
  · apply closed_hull_convex
    by_contra hLi
    push_neg at hLi
    have ⟨i, hLi⟩ := hLi
    have hc₁ : colin u v (L i) := by
      apply sub_collinear_right_symm' hc
      · have hLivw : (L i) ∈ closed_hull (to_segment u w) \ closed_hull (to_segment u v) := by
          by_contra honctra
          have hLiuw : (L i) ∈ closed_hull (to_segment u w) := by
            apply hLsub
            apply boundary_in_closed
            apply boundary_seg' hL01
          have hLiuv : (L i) ∈ closed_hull (to_segment u v) := by
            tauto_set
          tauto_set
        rw [clopen_left] at hLivw
        exact hLivw.1
        apply hc
      · by_contra hcontra
        rw [hcontra] at hLi
        have hvcl : v ∈ closed_hull (to_segment u v) := by
          apply boundary_in_closed
          have huv : u ≠ v := by
            exact (middle_not_boundary_colin hc).1
          have hvinboundary : v ∈ boundary (to_segment u v) := by
            apply boundary_seg' huv 1
          exact hvinboundary
        tauto_set
    have hc₂ : colin x v (L i) := by
      apply sub_collinear_right' hc₁ hx
      intro h;
      rw [h] at hxL
      exact hv hxL
    refine hv (open_segment_sub ?_ ?_ hc₂.2)
    · intro j
      by_cases hj0 : j = 0
      rw [hj0]
      rw[to_segment]
      apply open_sub_closed _ hxL
      have hj1 : j = 1 := by
        fin_cases j
        simp only [Fin.zero_eta, Fin.isValue, not_true_eq_false] at hj0
        simp only [Fin.mk_one, Fin.isValue]
      rw [hj1]
      rw [to_segment]
      apply boundary_in_closed
      apply boundary_seg' hL01
    · rw [to_segment, to_segment]
      by_contra hcontra
      rw [hcontra] at hxL
      apply boundary_not_in_open
      apply boundary_seg' hL01
      apply i
      apply hxL

--test

def ClosedSymSeg : Sym2 ℝ² → Set ℝ² :=
  Sym2.lift ⟨fun a b ↦ closed_hull (to_segment a b), by
  intro _ _
  convert reverse_segment_closed_hull
  simp only [reverse_segment_to_segment]⟩


lemma colin_sub {u v w : ℝ²} (h : colin u v w) {L : Segment}
    (hLsub : closed_hull L ⊆ closed_hull (to_segment u w)) (hLv : v ∉ open_hull L) :
    closed_hull L ⊆ closed_hull (to_segment u v) ∨ closed_hull L ⊆ closed_hull (to_segment v w) := by

    have hxl : ∃ x, x ∈ open_hull L := by
     apply open_pol_nonempty
     linarith
    have hvw : v ≠ w := by
      apply (middle_not_boundary_colin h).2
    rcases hxl with ⟨x, hx⟩
    by_cases hxl' : x ∈ closed_hull (to_segment u v)
    constructor
    · exact (colin_sub_aux h hLsub hLv hx hxl')
    have hrevwu : closed_hull (to_segment w u) = closed_hull (reverse_segment (to_segment u w)) := by
      rw [ reverse_segment_to_segment]
    have hLsubrev : closed_hull L ⊆ closed_hull (to_segment w u) := by
      rw [hrevwu]
      rw [reverse_segment_closed_hull]
      apply hLsub
    have hxl'': x ∈ closed_hull (to_segment v w) := by
       have hxlaux' : x ∈ closed_hull (to_segment u w) := by
         apply hLsub
         apply open_sub_closed _ hx
       have hxlaux: closed_hull (to_segment u w) = closed_hull (to_segment u v) ∪ closed_hull (to_segment v w) := by
         apply colin_decomp_closed h
       tauto_set
    have hxl''rev: x ∈ closed_hull (to_segment w v) := by
      rw [← reverse_segment_closed_hull]
      rw [reverse_segment_to_segment]
      exact hxl''
    · right
      have hlrevvw : closed_hull L ⊆ closed_hull (to_segment w v) := by
        apply colin_sub_aux (colin_reverse h) hLsubrev hLv hx hxl''rev
      rw [← reverse_segment_to_segment] at hlrevvw
      rw [reverse_segment_closed_hull] at hlrevvw
      exact hlrevvw



lemma closed_hull_eq_imp_eq_triv {u v x y : ℝ²} (huv : u = v)
    (h : closed_hull (to_segment u v) = closed_hull (to_segment x y)) :
    u = x ∧ u = y := by
  rw [(segment_triv' (L := to_segment u v)).1 huv] at h
  have hxy : x = y := by
    refine (segment_triv (L := to_segment x y)).2 ?_
    exact ⟨u, by simp [to_segment, ←h]⟩
  rw [(segment_triv' (L := to_segment x y)).1 hxy] at h
  simp_all [to_segment]


lemma closed_hull_eq_imp_eq_or_rev_seg_aux {u v x y : ℝ²}
    (h : closed_hull (to_segment u v) = closed_hull (to_segment x y))
    : u = x ∨ u = y := by
  by_cases huv : u = v
  · simp [closed_hull_eq_imp_eq_triv huv h]
  · have hxy : x ≠ y := by
      intro hxy
      apply huv
      have this := closed_hull_eq_imp_eq_triv hxy h.symm
      rw [←this.1, ←this.2]
    by_contra hc; push_neg at hc
    have hu : u ∈ open_hull (to_segment u v) := by
      refine open_segment_sub' (L₁ := to_segment x y) (by simp only [h, subset_refl]) hxy ?_
      rw [←open_closed_hull_minus_boundary, Set.mem_diff, ←h, boundary_seg_set hxy]
      refine ⟨by convert corner_in_closed_hull (P := to_segment u v) (i := 0 ),?_⟩
      simp_all [to_segment]
    apply Set.eq_empty_iff_forall_not_mem.1 (boundary_int_open_empty (P := to_segment u v)) u
    exact ⟨boundary_seg' huv 0 ,hu⟩

lemma closed_hull_eq_imp_eq_or_rev_seg {u v x y : ℝ²}
  (h : closed_hull (to_segment u v) = closed_hull (to_segment x y))
    : (u = x ∧ v = y) ∨ (u = y ∧ v = x) := by
  cases' closed_hull_eq_imp_eq_or_rev_seg_aux h with hu hu <;>
    (
      rw [←reverse_segment_closed_hull] at h
      cases' closed_hull_eq_imp_eq_or_rev_seg_aux h with hv hv
    )
  all_goals try simp_all [to_segment]
  all_goals simp_all [closed_hull_eq_imp_eq_triv (by rfl) h]

lemma closed_hull_eq_imp_eq_or_rev {L₁ L₂ : Segment}
    (h: closed_hull L₁ = closed_hull L₂) : L₁ = L₂ ∨ L₁ = reverse_segment L₂ := by
  cases' closed_hull_eq_imp_eq_or_rev_seg h with hsame hrev
  · left
    ext i j
    fin_cases i <;> fin_cases j <;> simp_all
  · right
    ext i j
    fin_cases i <;> fin_cases j <;> simp_all [reverse_segment, to_segment]


lemma closed_hull_eq_imp_open_hull_eq {L₁ L₂ : Segment}
    (h: closed_hull L₁ = closed_hull L₂) : open_hull L₁ = open_hull L₂ := by
  cases' closed_hull_eq_imp_eq_or_rev h with h h <;> rw [h]
  exact reverse_segment_open_hull

lemma closed_hull_eq_imp_boundary_eq {L₁ L₂ : Segment}
    (h: closed_hull L₁ = closed_hull L₂) : boundary L₁ = boundary L₂ := by
  cases' closed_hull_eq_imp_eq_or_rev h with h h <;> rw [h]
  exact reverse_segment_boundary




/- More stuff about infinite lines in ℝ²-/


noncomputable def line_par (v₁ v₂ : ℝ²) : ℝ → ℝ² := fun t ↦ v₁ + t • v₂


lemma seg_par_injective {v₁ v₂ : ℝ²} (h : v₂ ≠ 0) : (line_par v₁ v₂).Injective := by
  intro t₁ t₂ ht
  rw [line_par, line_par, add_right_inj] at ht
  have this := sub_eq_zero_of_eq ht
  rwa [←sub_smul, propext (smul_eq_zero_iff_left h), sub_eq_zero] at this


lemma seg_par₀ {v₁ v₂ : ℝ²} : line_par v₁ v₂ 0 = v₁ := by
  simp only [line_par, zero_smul, add_zero]

lemma seg_par_closed_self {L : Segment} :
  closed_hull L = line_par (L 0) (seg_vec L) '' (Set.Icc 0 1 : Set ℝ) := closed_segment_interval_im

lemma seg_par_open_self {L : Segment} :
  open_hull L = line_par (L 0) (seg_vec L) '' (Set.Ioo 0 1 : Set ℝ) := open_segment_interval_im


lemma line_par_scalar_Icc {a b t : ℝ} {v₁ v₂ : ℝ²} (ht : 0 < t):
    line_par v₁ (t • v₂) '' (Set.Icc a b) = line_par v₁ (v₂) '' (Set.Icc (t * a) (t * b)) := by
  ext x
  rw [Set.mem_image, Set.mem_image]
  constructor
  · intro ⟨k, habk, hx⟩
    refine ⟨t * k, ⟨?_, ?_⟩, ?_⟩
    · exact (mul_le_mul_iff_of_pos_left ht).mpr habk.1
    · exact (mul_le_mul_iff_of_pos_left ht).mpr habk.2
    · rw [←hx, line_par, line_par]
      module
  · intro ⟨k, habk, hx⟩
    refine ⟨k / t, ⟨?_, ?_⟩, ?_⟩
    · exact (le_div_iff₀' ht).mpr habk.1
    · exact (div_le_iff₀' ht).mpr habk.2
    · rw [←hx, line_par, line_par]
      match_scalars
      · rfl
      · field_simp

lemma line_par_neg {a b : ℝ} {v₁ v₂ : ℝ²} :
    line_par v₁ (v₂) '' (Set.Icc a b) = line_par v₁ (- v₂) '' (Set.Icc (-b) (-a)) := by
  ext x
  rw [Set.mem_image, Set.mem_image]
  constructor <;> (
  intro ⟨k, habk, hx⟩
  refine ⟨-k, ⟨?_, ?_⟩, ?_⟩
  · linarith [habk.2]
  · linarith [habk.1]
  · rw [←hx, line_par, line_par]
    module)



lemma line_par_scalar_Icc' {a b t : ℝ} {v₁ v₂ : ℝ²} (ht : t < 0):
    line_par v₁ (t • v₂) '' (Set.Icc a b) = line_par v₁ (v₂) '' (Set.Icc (t * b) (t * a)) := by
  have ht : 0 < - t := by linarith
  rw [line_par_neg, ←neg_smul, line_par_scalar_Icc ht, neg_mul_neg, neg_mul_neg]

lemma line_par_trans_Icc {a b t : ℝ} {v₁ v₂ : ℝ²} :
    line_par (v₁ + t • v₂) (v₂) '' (Set.Icc a b) = line_par v₁ (v₂) '' (Set.Icc (a + t) (b + t)) := by
  ext x
  rw [Set.mem_image, Set.mem_image]
  constructor
  · intro ⟨k, habk, hx⟩
    refine ⟨k + t, ⟨by linarith [habk.1],by linarith [habk.2]⟩, ?_⟩
    rw [←hx, line_par, line_par]
    module
  · intro ⟨k, habk, hx⟩
    refine ⟨k - t, ⟨by linarith [habk.1],by linarith [habk.2]⟩, ?_⟩
    rw [←hx, line_par, line_par]
    module

lemma line_par_closed {a b : ℝ} {v₁ v₂ : ℝ²} (hab : a ≤ b) :
    line_par v₁ v₂ '' (Set.Icc a b) = closed_hull (to_segment (v₁ + a • v₂) (v₁ + b • v₂)) := by
  by_cases hab' : a = b
  · rw [hab']
    simp only [line_par, Set.Icc_self, Set.image_singleton]
    convert (segment_triv'.1 ?_).symm <;> simp [to_segment]
  · have hab : a < b := lt_of_le_of_ne hab hab'
    have hbsuba : 0 < b - a := by linarith
    ext x
    constructor
    · intro h
      rw [Set.mem_image] at h
      have ⟨t, htab, htx⟩ := h
      refine ⟨fun | 0 => (b - t)/(b-a) | 1 => (t - a)/(b-a), ⟨?_,?_⟩ , ?_⟩
      · intro i
        fin_cases i
        · simp only
          exact div_nonneg (by linarith [htab.2]) (by linarith [hbsuba])
        · simp only
          exact div_nonneg (by linarith [htab.1]) (by linarith [hbsuba])
      · field_simp
      · rw [←htx]
        simp [to_segment, line_par]
        match_scalars
        · field_simp
        · field_simp
          ring
    · intro ⟨α,hα,hx⟩
      rw [Set.mem_image]
      have hα0 := simplex_closed_sub_fin2 hα 0
      have hα1 := simplex_closed_sub_fin2 hα 1
      simp only [Fin.isValue] at hα0 hα1
      refine ⟨α 0 * a + α 1 * b, ?_,?_⟩
      · refine ⟨?_,?_⟩
        · rw [hα0, sub_mul, one_mul, add_comm_sub, le_add_iff_nonneg_right]
          apply sub_nonneg_of_le
          exact mul_le_mul_of_nonneg_left (by assumption) (hα.1 1)
        · rw [hα1, sub_mul, one_mul, ←add_comm_sub]
          apply add_le_of_nonpos_left
          rw [tsub_nonpos]
          exact mul_le_mul_of_nonneg_left (by assumption) (hα.1 0)
      · rw [←hx]
        simp only [line_par, Fin.isValue, hα0, to_segment, Fin.sum_univ_two, smul_add]
        module

lemma line_par_open {a b : ℝ} {v₁ v₂ : ℝ²} (hab : a < b) :
    line_par v₁ v₂ '' (Set.Ioo a b) = open_hull (to_segment (v₁ + a • v₂) (v₁ + b • v₂)) := by
  have hbsuba : 0 < b - a := by linarith
  ext x
  constructor
  · intro h
    rw [Set.mem_image] at h
    have ⟨t, htab, htx⟩ := h
    refine ⟨fun | 0 => (b - t)/(b-a) | 1 => (t - a)/(b-a), ⟨?_,?_⟩ , ?_⟩
    · intro i
      fin_cases i
      · simp only
        exact div_pos (by linarith [htab.2]) (by linarith [hbsuba])
      · simp only
        exact div_pos (by linarith [htab.1]) (by linarith [hbsuba])
    · field_simp
    · rw [←htx]
      simp [to_segment, line_par]
      match_scalars
      · field_simp
      · field_simp
        ring
  · intro ⟨α,hα,hx⟩
    rw [Set.mem_image]
    have hα0 := simplex_open_sub_fin2 hα 0
    have hα1 := simplex_open_sub_fin2 hα 1
    simp only [Fin.isValue] at hα0 hα1
    refine ⟨α 0 * a + α 1 * b, ?_,?_⟩
    · refine ⟨?_,?_⟩
      · rw [hα0, sub_mul, one_mul, add_comm_sub]
        apply lt_add_of_pos_right
        rwa [sub_pos, mul_lt_mul_left (hα.1 1)]
      · rwa [hα1, sub_mul, one_mul, ←add_comm_sub, add_lt_iff_neg_right, sub_neg, mul_lt_mul_left (hα.1 0)]
    · rw [←hx]
      simp only [line_par, Fin.isValue, hα0, to_segment, Fin.sum_univ_two, smul_add]
      module


lemma seg_vec_mul {L₁ L₂ : Segment} (h : closed_hull L₁ ⊆ closed_hull L₂) :
    ∃ t : ℝ, seg_vec L₁ = t • (seg_vec L₂) := by
  have ⟨α0, hα0, h0⟩ := h (corner_in_closed_hull (P := L₁) (i := 0))
  have ⟨α1, hα1, h1⟩ := h (corner_in_closed_hull (P := L₁) (i := 1))
  use α1 1 - α0 1
  have hα00 := simplex_closed_sub_fin2 hα0 0
  have hα10 := simplex_closed_sub_fin2 hα1 0
  simp [seg_vec, ←h0, ←h1,hα00, hα10]
  module


lemma seg_par {L₁ L₂ : Segment} (h₁ : L₁ 0 ≠ L₁ 1) (h₂ : closed_hull L₁ ⊆ closed_hull L₂) :
    ∃ a b, closed_hull L₂ = line_par (L₁ 0) (seg_vec L₁) '' (Set.Icc a b : Set ℝ) := by
  have ⟨t, ht⟩ := seg_vec_mul h₂
  have htn : t ≠ 0 := by
    intro hcontra
    rw [hcontra, zero_smul] at ht
    exact h₁ ((seg_vec_zero_iff L₁).mp ht)
  have ⟨k, hk⟩ := seg_vec_co (x := L₂ 0) (y := L₁ 0) corner_in_closed_hull (h₂ corner_in_closed_hull)
  by_cases htnonneg : 0 ≤ t
  · have htpos : 0 < t := lt_of_le_of_ne htnonneg htn.symm
    simp_rw [ht, line_par_scalar_Icc htpos, hk, line_par_trans_Icc, closed_segment_interval_im]
    use (-k)/t, (1-k)/t
    unfold line_par
    have h0 : (t * (-k / t) + k) = 0 := by
      field_simp
      ring
    have h1 : (t * ((1 - k) / t) + k) = 1 := by
      field_simp
    rw [h0, h1]
  · simp_rw [ht, line_par_scalar_Icc' (by linarith), hk, line_par_trans_Icc, closed_segment_interval_im]
    use (1-k)/t, (-k)/t
    unfold line_par
    have h0 : (t * (-k / t) + k) = 0 := by
      field_simp
      ring
    have h1 : (t * ((1 - k) / t) + k) = 1 := by
      field_simp
    rw [h0, h1]

lemma seg_par_open_hull {L : Segment} {a b : ℝ} {v₁ v₂ : ℝ²} (hab : a < b)
    (hc : closed_hull L = line_par v₁ v₂ '' (Set.Icc a b : Set ℝ)) :
    open_hull L = line_par v₁ v₂ '' (Set.Ioo a b : Set ℝ) := by
  rw [line_par_closed (by linarith)] at hc
  rw [closed_hull_eq_imp_open_hull_eq hc]
  exact (line_par_open hab).symm

lemma seg_par_boundary {L : Segment} {a b : ℝ} {v₁ v₂ : ℝ²} (hab : a < b) (h : v₂ ≠ 0)
    (hc : closed_hull L = line_par v₁ v₂ '' (Set.Icc a b : Set ℝ)) :
    boundary L = line_par v₁ v₂ '' {a,b} := by
  rw [boundary, hc, seg_par_open_hull hab hc, ←Set.image_diff (seg_par_injective h) _ _]
  apply (Set.image_eq_image (seg_par_injective h)).mpr
  exact Set.Icc_diff_Ioo_same (le_of_lt hab)

lemma seg_par_nontrivial {L : Segment} {a b : ℝ} {v₁ v₂ : ℝ²} (hL : L 0 ≠ L 1)
    (hc : closed_hull L = line_par v₁ v₂ '' (Set.Icc a b : Set ℝ)) :
  a < b := by
  by_contra hab
  have hS : Set.Subsingleton (closed_hull L) := by
    rw [hc]
    exact Set.Subsingleton.image (by rw [Set.subsingleton_Icc_iff]; linarith) _
  exact hL (hS corner_in_closed_hull corner_in_closed_hull)


lemma interval_intersection {a₁ a₂ b₁ b₂: ℝ} (hx₁ : Set.Icc 0 1 ⊆ Set.Icc a₁ b₁)
  (hx₂ : Set.Icc 0 1 ⊆ Set.Icc a₂ b₂)
  (ha : a₂ ∉ Set.Ioo a₁ b₁) (hb : b₂ ∉ Set.Ioo a₁ b₁) : Set.Icc a₁ b₁ ⊆ Set.Icc a₂ b₂ := by
  intro y ⟨hyl, hyu⟩
  have ha₁0 : a₁ ≤ 0 := (hx₁ ⟨by linarith, by linarith⟩).1
  have ha₂0 : a₂ ≤ 0 := (hx₂ ⟨by linarith, by linarith⟩).1
  have hb₁1 : 1 ≤ b₁ := (hx₁ ⟨by linarith, by linarith⟩).2
  have hb₂1 : 1 ≤ b₂ := (hx₂ ⟨by linarith, by linarith⟩).2
  refine ⟨?_,?_⟩
  · by_contra hy
    exact ha ⟨by linarith, by linarith⟩
  · by_contra hy
    exact hb ⟨by linarith, by linarith⟩


lemma seg_sub_seg {L₁ L₂ L₃ : Segment}  (h₁ : L₁ 0 ≠ L₁ 1) (h₂ : closed_hull L₁ ⊆ closed_hull L₂)
    (h₃ : closed_hull L₁ ⊆ closed_hull L₃) (h₂₃ : Disjoint (open_hull L₂) (boundary L₃))
  : closed_hull L₂ ⊆ closed_hull L₃ := by
  have ⟨a₂,b₂, hab₂⟩ := seg_par h₁ h₂
  have ⟨a₃,b₃, hab₃⟩ := seg_par h₁ h₃
  rw [hab₂, hab₃]
  have segNeqZero := ((seg_vec_nonzero_iff _).2 h₁)
  have fInj := seg_par_injective (v₁ := L₁ 0) segNeqZero
  have ha₂leqb₂ : a₂ < b₂ := seg_par_nontrivial (seg_nontriv_sub h₂ h₁) hab₂
  have ha₃leqb₃ : a₃ < b₃ := seg_par_nontrivial (seg_nontriv_sub h₃ h₁) hab₃
  refine Set.image_mono (interval_intersection ?_ ?_ ?_ ?_)
  · rw [seg_par_closed_self (L := L₁), hab₂] at h₂
    exact (Set.image_subset_image_iff fInj).mp h₂
  · rw [seg_par_closed_self (L := L₁), hab₃] at h₃
    exact (Set.image_subset_image_iff fInj).mp h₃
  · intro ha
    rw [←Function.Injective.mem_set_image fInj, ←seg_par_open_hull ha₂leqb₂ hab₂] at ha
    apply Set.disjoint_left.1 h₂₃ ha
    rw [seg_par_boundary ha₃leqb₃ segNeqZero hab₃]
    simp
  · intro hb
    rw [←Function.Injective.mem_set_image fInj, ←seg_par_open_hull ha₂leqb₂ hab₂] at hb
    apply Set.disjoint_left.1 h₂₃ hb
    rw [seg_par_boundary ha₃leqb₃ segNeqZero hab₃]
    simp


lemma seg_open_hull_infinite {L: Segment}  (h : L 0 ≠ L 1) :
  Set.Infinite (open_hull L) := by
  rw [open_segment_interval_im]
  refine Set.Infinite.image ?_ (Set.Ioo_infinite (by norm_num))
  intro a ha b hb heq
  rw [seg_vec, add_left_cancel_iff, ←sub_eq_zero, ←sub_smul, smul_eq_zero] at heq
  cases' heq with this this
  · linarith
  · exfalso
    exact h ((seg_vec_zero_iff L).mp this)


lemma seg_closed_hull_infinite {L: Segment}  (h : L 0 ≠ L 1) :
    Set.Infinite (closed_hull L) :=
  Set.Infinite.mono (open_sub_closed L) (seg_open_hull_infinite h)


lemma closed_segment_sub_union_segment {A : Finset Segment} {L : Segment}
    (hL : L 0 ≠ L 1)
    (hSub : closed_hull L ⊆ ⋃ S ∈ A, closed_hull S)
    (hA : ∀ S ∈ A, Disjoint (open_hull L) (boundary S))
    : ∃ S ∈ A, closed_hull L ⊆ closed_hull S := by
  have hMap : ∀ (x : closed_hull L), ∃ (S : A), x.val ∈ closed_hull S.val := by
    intro x
    have ⟨S,hS,hxS⟩ := Set.mem_iUnion₂.1 (hSub x.2)
    use ⟨S,hS⟩
  choose fL fLh using hMap
  have hInf := Set.infinite_coe_iff.mpr (seg_closed_hull_infinite hL)
  have ⟨x₁, x₂, hxS, hneq⟩ := Function.not_injective_iff.1 (not_injective_infinite_finite fL)
  refine ⟨fL x₁,by simp only [coe_mem],?_⟩
  refine seg_sub_seg (L₁ := to_segment x₁.val x₂.val) ?_ ?_ ?_ ?_
  · simp_all only [ne_eq, Subtype.forall, to_segment, Subtype.coe_ne_coe.mpr hneq,
    not_false_eq_true]
  · apply closed_hull_convex
    intro i
    fin_cases i <;> simp [to_segment]
  · apply closed_hull_convex
    intro i
    fin_cases i
    · simp [to_segment, fLh x₁]
    · simp [hxS, to_segment, fLh x₂]
  · exact hA _ (coe_mem (fL x₁))




/- Convex in the sense that it contains line segments. -/
lemma open_hull_convex {n : ℕ} {P : Fin n → ℝ²} {x y : ℝ²}
    (hx : x ∈ open_hull P) (hy : y ∈ open_hull P)
    : closed_hull (to_segment x y) ⊆ open_hull P := by
  intro z hz
  have ⟨αx, hα, hαx⟩ := hx
  have ⟨βy, hβ, hβy⟩ := hy
  have ⟨γz, hγ, hγz⟩ := hz
  use (fun i ↦ γz 0 * αx i + γz 1 * βy i)
  refine ⟨⟨?_,?_⟩,?_ ⟩
  · intro i
    simp only [Fin.isValue]
    have ⟨k, hk⟩ := simplex_exists_co_pos hγ
    fin_cases k
    · refine gt_of_ge_of_gt (b := γz 0 * αx i + 0) ?_ ?_
      · gcongr
        exact Left.mul_nonneg (hγ.1 1) (le_of_lt (hβ.1 i))
      · rw [add_zero]
        exact mul_pos hk (hα.1 i)
    · refine gt_of_ge_of_gt (b := 0 + γz 1 * βy i) ?_ ?_
      · gcongr
        exact Left.mul_nonneg (hγ.1 0) (le_of_lt (hα.1 i))
      · rw [zero_add]
        exact mul_pos hk (hβ.1 i)
  · simp only [Fin.isValue, sum_add_distrib,
      ←(mul_sum univ _ (γz 0)), ←(mul_sum univ _ (γz 1)), hα.2, hβ.2, mul_one,
      ←Fin.sum_univ_two, hγ.2]
  · simp only [Fin.isValue, add_smul, sum_add_distrib, mul_smul, ←smul_sum,
        hαx, hβy, ←hγz, to_segment, Fin.sum_univ_two]



lemma open_sub_closed_sub (S L : Segment) (h : open_hull S ⊆ open_hull L) :
    closed_hull S ⊆ closed_hull L := by
  by_cases hS : seg_vec S = 0
  · rw [seg_vec_zero_open_hull hS] at h
    rw [seg_vec_zero_closed_hull hS]
    trans (open_hull L)
    · exact h
    · exact open_sub_closed _
  · have ⟨x, hx, y, hy, hxy⟩
      := infinite_imp_two_distinct_el (seg_open_hull_infinite (L := S) (by rwa [←seg_vec_nonzero_iff]))
    have hxyS : closed_hull (to_segment x y) ⊆ open_hull S := open_hull_convex hx hy
    refine seg_sub_seg (L₁ := to_segment x y) hxy ?_ ?_ ?_
    · trans (open_hull S)
      · exact hxyS
      · exact open_sub_closed _
    · trans (open_hull L)
      · trans open_hull S
        · exact hxyS
        · exact h
      · exact open_sub_closed _
    · apply Set.disjoint_of_subset h (fun ⦃a⦄ a ↦ a)
      rw [@Set.disjoint_iff_inter_eq_empty, Set.inter_comm]
      exact boundary_int_open_empty


noncomputable def segment_around_x (x y : ℝ²) (ε₁ ε₂ : ℝ)
    : Segment := to_segment (x + (1 * ε₁) • y) (x + (-1 * ε₂) • y)

lemma open_hull_segment_around {x y : ℝ²} {ε₁ ε₂ : ℝ} (h₁ : 0 < ε₁)
    (h₂ : 0 < ε₂) : x ∈ open_hull (segment_around_x x y ε₁ ε₂) := by
  have hs   : ε₁ + ε₂ > 0 := by linarith
  use fun | 0 => ε₂ / (ε₁ + ε₂) | 1 => ε₁ / (ε₁ + ε₂)
  refine ⟨⟨?_,?_⟩ ,?_⟩
  · intro i
    fin_cases i <;> simp_all [div_pos]
  · field_simp [add_comm]
  · ext i
    field_simp [segment_around_x, to_segment]
    fin_cases i <;> ring

lemma open_hull_segment_around_non_trivial {x y : ℝ²} {ε₁ ε₂ : ℝ}
    (hy : y ≠ 0) (hε : ε₁ + ε₂ ≠ 0) : seg_vec (segment_around_x x y ε₁ ε₂) ≠ 0 := by
  simp only [seg_vec, segment_around_x, to_segment, neg_mul, one_mul, add_sub_add_left_eq_sub,
    ←sub_smul, ne_eq, smul_eq_zero, hy, or_false]
  intro hy
  apply hε
  rw [←neg_add', add_comm] at hy
  exact neg_eq_zero.mp hy




-- More lemmas about the triangle

lemma real_number_bound_aux {n : ℕ} {f g : Fin n → ℝ}
    (h₁ : ∀ i, 0 < f i) (h₂ : ∀ ε > 0, ∃ i, ε * g i ≤ - f i) : False := by
  revert h₂
  simp only [gt_iff_lt, imp_false, not_forall, Classical.not_imp, not_exists, not_le]
  by_cases hn : n = 0
  · use 1, by linarith
    intro contra
    rw [hn] at contra
    exact Fin.elim0 contra
  · have hN : (image (fun i ↦ |g i|) univ).Nonempty := by
      simp only [image_nonempty, univ_nonempty, univ_nonempty_iff, ←Fin.pos_iff_nonempty]
      exact Nat.zero_lt_of_ne_zero hn
    have hN₂ : (image (fun i ↦ f i) univ).Nonempty := by
      simp only [image_nonempty, univ_nonempty, univ_nonempty_iff, ←Fin.pos_iff_nonempty]
      exact Nat.zero_lt_of_ne_zero hn
    let M := Finset.max' (Finset.image (fun i ↦ |g i|)  (univ : Finset (Fin n))) hN
    let M₂ := Finset.min' (Finset.image (fun i ↦ f i)  (univ : Finset (Fin n))) hN₂
    have Mrw : M =  Finset.max' (Finset.image (fun i ↦ |g i|)  (univ : Finset (Fin n))) hN := rfl
    have Mrw₂ : M₂ = Finset.min' (Finset.image (fun i ↦ f i)  (univ : Finset (Fin n))) hN₂ := rfl
    have hMg : ∀ i, |g i| ≤ M := by
      rw [Mrw]
      by_contra hc
      push_neg at hc
      have ⟨i, hci⟩ := hc
      simp_rw [Finset.max'_lt_iff _ hN] at hc
      have ⟨j,hj⟩:= hc
      specialize hj (|g j|)
      simp_all
    have hMnonNeg : 0 ≤ M := le_trans (abs_nonneg _) (hMg ⟨0, Nat.zero_lt_of_ne_zero hn⟩)
    have hM₂pos : 0 < M₂ := by
      rw [Mrw₂, Finset.lt_min'_iff ]
      intro fi h
      rw [@mem_image] at h
      have ⟨i, _,hi⟩ := h
      rw [←hi]
      exact h₁ i
    by_cases hM₀ : M = 0
    · use 1, by norm_num
      intro i
      specialize h₁ i
      specialize hMg i
      rw [hM₀] at hMg
      have ht : g i = 0 := abs_nonpos_iff.mp hMg
      rw [ht]
      linarith
    · have hMpos : 0 < M := lt_of_le_of_ne hMnonNeg fun a ↦ hM₀ (id (Eq.symm a))
      use M₂ / (2 * M), (div_pos_iff_of_pos_left hM₂pos).mpr (by linarith)
      intro i
      rw [←mul_div_right_comm, lt_div_iff₀' (by linarith)]
      by_cases hgi : 0 ≤ g i
      · refine gt_of_ge_of_gt (b := 0) ?_ ?_
        · exact (mul_nonneg_iff_of_pos_left hM₂pos).mpr hgi
        · simp only [mul_neg, gt_iff_lt, Left.neg_neg_iff]
          refine mul_pos (by linarith) (h₁ i)
      · refine gt_of_ge_of_gt (b := - f i * M) ?_ ?_
        · simp_rw [←neg_le_neg_iff (a := M₂ * g i)]
          rw [mul_comm, neg_mul_eq_neg_mul, neg_mul_eq_neg_mul, InvolutiveNeg.neg_neg, mul_comm]
          refine mul_le_mul_of_nonneg ?_ ?_ ?_ hMnonNeg
          · rw [Mrw₂]
            apply Finset.min'_le
            rw [@mem_image]
            use i
            simp only [mem_univ, and_self]
          · convert hMg i using 1
            refine Eq.symm (abs_of_neg (by linarith))
          · exact le_of_lt hM₂pos
        · simp_rw [←neg_lt_neg_iff (a := -f i * M)]
          simp only [neg_mul, neg_neg, mul_neg]
          rw [mul_comm (a := 2 * M)]
          gcongr
          · exact h₁ i
          · linarith



lemma triangle_open_hull_open {T : Triangle} (hnonDeg : det T ≠ 0) {x: ℝ²}
    (y : ℝ²)
    (hx : x ∈ open_hull T) : ∃ (ε : ℝ), ε > 0 ∧ x + ε • y ∈ open_hull T := by
  by_contra hcontra
  push_neg at hcontra
  have habsurd : ∀ (ε : ℝ), ε > 0 → ∃ i, Tco T (x + ε • y) i ≤ 0 := by
    by_contra hc
    push_neg at hc
    have ⟨ε, hε, hi⟩ := hc
    apply hcontra ε hε
    rwa [open_triangle_iff hnonDeg]
  have habsurd₂ : ∀ ε > 0, ∃ i, ε * det₂ (Oside T i) y / det T ≤ -Tco T x i := by
    intro ε hε
    have ⟨l, hl⟩ := habsurd ε hε
    use l
    rw [Tco_line] at hl
    linarith
  rw [open_triangle_iff hnonDeg] at hx
  apply real_number_bound_aux hx (g := fun i ↦ det₂ (Oside T i) y / det T)
  intro ε hε
  have ⟨l, hl⟩ := habsurd ε hε
  use l
  rw [Tco_line] at hl
  rw [mul_div]
  linarith


lemma triangle_direction_sub {T : Triangle} {x : ℝ²} (hx : x ∈ closed_hull T)
    (hn : ∀ i, x ≠ T i) :
    ∃ L : Segment, L 0 ≠ L 1 ∧ x ∈ open_hull L ∧ closed_hull L ⊆ closed_hull T := by
  have ⟨α, hα, hαx⟩ := hx
  have hij : ∃ i j, α i ≠ 0 ∧ α j ≠ 0 ∧ T i ≠ T j:= by
    by_contra h
    push_neg at h
    have ⟨i, hi⟩ := simplex_exists_co_pos hα
    have ha : ∀ j, α j • T j = α j • T i := by
      intro j
      by_cases hj : α j = 0
      · simp [hj, zero_smul]
      · rw [h i j (by linarith) hj]
    apply hn i
    simp_rw [←hαx, Fin.sum_univ_three, ha 0, ha 1, ha 2, ←add_smul]
    rw [←Fin.sum_univ_three, hα.2, one_smul]
  have ⟨i,j,⟨h1,h2,h3⟩⟩ := hij
  have hijneq : i ≠ j := by intro this; apply h3; rw [this]
  use segment_around_x x (seg_vec (to_segment (T i) (T j))) (α i) (α j)
  have hαi := lt_of_le_of_ne (hα.1 i) h1.symm
  have hαj := lt_of_le_of_ne (hα.1 j) h2.symm
  refine ⟨?_,?_,?_⟩
  · rw [←seg_vec_nonzero_iff]
    apply open_hull_segment_around_non_trivial
    · rw [seg_vec_nonzero_iff]
      exact h3
    · linarith
  · exact open_hull_segment_around hαi hαj
  · apply closed_hull_convex
    intro k
    fin_cases k
    · use (fun l ↦ if l = i then 0 else (if l = j then (α i + α j) else α l))
      refine ⟨⟨?_,?_⟩ ,?_⟩
      · intro k
        simp only
        split
        · exact le_refl _
        · split
          · linarith
          · exact hα.1 k
      · rw [←hα.2, Fin.sum_univ_three, Fin.sum_univ_three]
        fin_cases i <;> fin_cases j <;> (simp_all) <;> ring
      · rw [segment_around_x, ←hαx]
        simp [Fin.sum_univ_three, to_segment, seg_vec]
        fin_cases i <;> fin_cases j <;> (simp_all) <;> module
    · use (fun l ↦ if l = j then 0 else (if l = i then (α i + α j) else α l))
      refine ⟨⟨?_,?_⟩ ,?_⟩
      · intro k
        simp only
        split
        · exact le_refl _
        · split
          · linarith
          · exact hα.1 k
      · rw [←hα.2, Fin.sum_univ_three, Fin.sum_univ_three]
        fin_cases i <;> fin_cases j <;> (simp_all) <;> ring
      · rw [segment_around_x, ←hαx]
        simp [Fin.sum_univ_three, to_segment, seg_vec]
        fin_cases i <;> fin_cases j <;> (simp_all) <;> module


lemma inward_pointing_vector_exists  {T : Triangle} {x : ℝ²}
    (hx : x ∈ closed_hull T) (hT : ¬(∀ i j, T i = T j))
    : ∃ y, x ≠ y ∧ open_hull (to_segment x y) ⊆ open_hull T := by
  have hy : ∃ y, y ∈ open_hull T ∧ x ≠ y := by
    by_contra hc
    push_neg at hc
    have h_all : ∀ i, T i = x := by
      apply open_hull_constant_rev
      ext y
      constructor
      · exact fun hy ↦ id (hc _ hy ).symm
      · rw [Set.mem_singleton_iff]
        intro h; rw [h]
        have ⟨z, hz⟩ := open_pol_nonempty (by linarith) T
        convert hz
        exact hc _ hz
    apply hT
    intro i j
    rw [h_all i, ←h_all j]
  have ⟨y, hy, hxy⟩ := hy
  use y, hxy
  intro z hz
  have ⟨αx, hα, hαx⟩ := hx
  have ⟨βy, hβ, hβy⟩ := hy
  have ⟨γz, hγ, hγz⟩ := hz
  use (fun i ↦ γz 0 * αx i + γz 1 * βy i)
  refine ⟨⟨?_,?_⟩,?_ ⟩
  · intro i
    simp only [Fin.isValue]
    refine gt_of_ge_of_gt (b := 0 + γz 1 * βy i) ?_ ?_
    · gcongr
      rw [mul_comm]
      exact Left.mul_nonneg (hα.1 i) (le_of_lt (hγ.1 0))
    · rw [zero_add]
      exact mul_pos (hγ.1 1) (hβ.1 i)
  · simp only [Fin.isValue, sum_add_distrib,
      ←(mul_sum univ _ (γz 0)), ←(mul_sum univ _ (γz 1)), hα.2, hβ.2, mul_one,
      ←Fin.sum_univ_two, hγ.2]
  · simp only [Fin.isValue, add_smul, sum_add_distrib, mul_smul, ←smul_sum,
        hαx, hβy, ←hγz, to_segment, Fin.sum_univ_two]

lemma seg_inter_open_triangle {T : Triangle} {S : Segment} (hDet : det T ≠ 0)
    (hST : closed_hull S ∩ open_hull T ≠ ∅) : open_hull S ∩ open_hull T ≠ ∅ := by
  rw [Mathlib.Tactic.PushNeg.ne_empty_eq_nonempty] at *
  have ⟨x, hxS, hxT⟩ := hST
  by_cases hxO : x ∈ open_hull S
  · exact ⟨x, hxO, hxT⟩
  · have hxB : x ∈ boundary S := Set.mem_diff_of_mem hxS hxO
    have hSn := boundary_seg_nonempty hxB
    rw [boundary_seg hSn, mem_coe, mem_image] at hxB
    have ⟨i, temp, hi⟩ := hxB
    wlog hi0 : i = 0
    · specialize this (S := reverse_segment S) hDet
      rw [reverse_segment_closed_hull, reverse_segment_open_hull] at this
      specialize this hST x hxS hxT hxO ?_ ?_ 0 (mem_univ _) ?_ rfl
      · use i + 1, by simp
        convert hi using 1
        fin_cases i <;> simp [reverse_segment, to_segment]
      · convert hSn.symm using 1
      · have hi1 : i = 1 := by fin_cases i <;> simp_all
        rw [hi1] at hi
        convert hi using 1
      · assumption
    · rw [hi0] at hi
      rw [←hi] at hxS hxT hxO
      clear hxB hi0 hi temp i
      have ⟨ε, hεpos, hε⟩ := triangle_open_hull_open hDet (seg_vec S) hxT
      have hTε : line_par (S 0) (seg_vec S) '' Set.Icc 0 ε ⊆ open_hull T := by
        rw [line_par_closed (by linarith)]
        refine open_hull_convex ?_ hε
        convert hxT
        simp only [Fin.isValue, zero_smul, add_zero]
      apply Set.Nonempty.mono (Set.inter_subset_inter_right (open_hull S) hTε)
      rw [seg_par_open_self]
      apply Set.Nonempty.mono (Set.image_inter_subset _ _ _)
      rw [Set.image_nonempty]
      use min (1/2) ε
      refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
      · exact lt_min (by norm_num) (hεpos)
      · exact min_lt_of_left_lt (by norm_num)
      · exact le_min (by norm_num) (le_of_lt hεpos)
      · exact min_le_right _ _



lemma disjoint_opens_implies_disjoint_open_closed {T₁ T₂ : Triangle}
  (hT : Disjoint (open_hull T₁) (open_hull T₂)) (hDet : det T₂ ≠ 0) :
    Disjoint (closed_hull T₁) (open_hull T₂) := by
  by_cases htriv : ∀ i j, T₁ i = T₁ j
  · convert hT using 1
    have hTc : T₁ = fun i ↦ T₁ 0 := by
      ext i
      rw [htriv i 0]
    rw [hTc, closed_hull_constant (by norm_num), open_hull_constant (by norm_num)]
  · rw [@Set.disjoint_right]
    intro x hxT₂ hxT₁
    have ⟨y, hxy, hS⟩ := inward_pointing_vector_exists hxT₁ htriv
    have hContra := (seg_inter_open_triangle (T := T₂) (S := to_segment x y) hDet ?_)
    · rw [@Set.disjoint_iff_inter_eq_empty] at hT
      apply hContra
      refine Set.subset_eq_empty (s := ∅) ?_ rfl
      rw [←hT]
      exact Set.inter_subset_inter hS fun ⦃a⦄ a ↦ a
    · rw [@Mathlib.Tactic.PushNeg.ne_empty_eq_nonempty]
      use x
      exact ⟨by exact corner_in_closed_hull (i := 0) (P := to_segment x y), hxT₂⟩
