import Mathlib
import Mathlib.Tactic

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

open Classical
open Finset


-- Shorthand for defining an element of ℝ²
def v (x y : ℝ) : ℝ² := fun | 0 => x | 1 => y

@[simp]
lemma v₀_val {x y : ℝ} : (v x y) 0 = x := rfl
@[simp]
lemma v₁_val {x y : ℝ} : (v x y) 1 = y := rfl


-- Definition of an n-dimensional standard simplex.
def closed_simplex (n : ℕ)  : Set (Fin n → ℝ) := {α | (∀ i, 0 ≤ α i) ∧ ∑ i, α i = 1}
def open_simplex   (n : ℕ)  : Set (Fin n → ℝ) := {α | (∀ i, 0 < α i) ∧ ∑ i, α i = 1}

/-
  The Fin n → ℝ² in the following definitions represents the vertices of a polygon.
  Beware: Whenever the n vertices do not define an n-gon, i.e. a vertex lies within the
  convex hull of the others, the open_hull does not give the topological interior of the closed
  hull.

  Also when f i = P for all i, both the closed_hull and open_hull are {P i}.
-/
def closed_hull {n : ℕ} (f : Fin n → ℝ²) : Set ℝ² := (fun α ↦ ∑ i, α i • f i) '' closed_simplex n
def open_hull   {n : ℕ} (f : Fin n → ℝ²) : Set ℝ² := (fun α ↦ ∑ i, α i • f i) '' open_simplex n


/- Corner of the standard simplex.-/
def simplex_vertex {n : ℕ} (i : Fin n) : Fin n → ℝ :=
    fun j ↦ if i = j then 1 else 0

lemma simplex_vertex_in_simplex {n : ℕ} {i : Fin n} : simplex_vertex i ∈ closed_simplex n := by
  exact ⟨fun j ↦ by by_cases h : i = j <;> simp [simplex_vertex, h], by simp [simplex_vertex]⟩

@[simp]
lemma simplex_vertex_image {n : ℕ} {i : Fin n} (f : Fin n → ℝ²) :
    ∑ k, (simplex_vertex i k) • f k = f i := by simp [simplex_vertex]

@[simp]
lemma corner_in_closed_hull {n : ℕ} {i : Fin n} {P : Fin n → ℝ²} : P i ∈ closed_hull P := by
  exact ⟨simplex_vertex i, simplex_vertex_in_simplex, by simp⟩

lemma closed_hull_constant {n : ℕ} {P : ℝ²} (hn : n ≠ 0):
    closed_hull (fun (_ : Fin n) ↦ P) = {P} := by
  ext _
  constructor
  · intro ⟨_, hα, hαv⟩
    simp [←hαv, ←sum_smul, hα.2, one_smul, Set.mem_singleton_iff]
  · intro hv; rw [hv]
    exact corner_in_closed_hull (i := ⟨0, Nat.zero_lt_of_ne_zero hn⟩)

lemma open_pol_nonempty {n : ℕ} (hn : 0 < n) (P : Fin n → ℝ²) : ∃ x, x ∈ open_hull P := by
  use ∑ i, (1/(n : ℝ)) • P i, fun _ ↦ (1/(n : ℝ))
  exact ⟨⟨fun _ ↦ by simp [hn], by simp; exact (mul_inv_cancel₀ (by simp; linarith))⟩, by simp⟩

lemma open_sub_closed_simplex {n : ℕ} : open_simplex n ⊆ closed_simplex n :=
  fun _ ⟨hαpos, hαsum⟩ ↦ ⟨fun i ↦ by linarith [hαpos i], hαsum⟩

lemma open_sub_closed {n : ℕ} (P : Fin n → ℝ²) : open_hull P ⊆ closed_hull P :=
  Set.image_mono open_sub_closed_simplex


/- Implications of the requirements that (∀ i, 0 ≤ α i),  ∑ i, α i = 1. -/

lemma simplex_co_eq_1 {n : ℕ} {α : Fin n → ℝ} {i : Fin n}
    (h₁ : α ∈ closed_simplex n) (h₂ : α i = 1) : ∀ j, j ≠ i → α j = 0 := by
  by_contra hcontra; push_neg at hcontra
  have ⟨j, hji, hj0⟩ := hcontra
  rw [←lt_self_iff_false (1 : ℝ)]
  calc
    1 = α i               := h₂.symm
    _ < α i + α j         := by rw [lt_add_iff_pos_right]; exact lt_of_le_of_ne (h₁.1 j) (hj0.symm)
    _ = ∑(k ∈ {i,j}), α k := (sum_pair hji.symm).symm
    _ ≤ ∑ k, α k          := sum_le_univ_sum_of_nonneg h₁.1
    _ = 1                 := h₁.2

lemma simplex_exists_co_pos {n : ℕ} {α : Fin n → ℝ} (h : α ∈ closed_simplex n)
    : ∃ i, 0 < α i := by
  by_contra hcontra; push_neg at hcontra
  have t : 1 ≤ (0: ℝ)  := by
    calc
      1 = ∑ i, α i        := h.2.symm
      _ ≤ ∑ (i: Fin n), 0 := sum_le_sum fun i _ ↦ hcontra i
      _ = 0               := Fintype.sum_eq_zero _ (fun _ ↦ rfl)
  linarith

lemma simplex_co_leq_1 {n : ℕ} {α : Fin n → ℝ}
    (h₁ : α ∈ closed_simplex n) : ∀ i, α i ≤ 1 := by
  by_contra hcontra; push_neg at hcontra
  have ⟨i,hi⟩ := hcontra
  rw [←lt_self_iff_false (1 : ℝ)]
  calc
    1   < α i             := hi
    _   = ∑ k ∈ {i}, α k  := (sum_singleton _ _).symm
    _   ≤ ∑ k, α k        := sum_le_univ_sum_of_nonneg h₁.1
    _   = 1               := h₁.2


/- Vertex set of polygon P₁ lies inside the closed hull of polygon P₂ implies
    the closed hull of P₁ lies inside the closed hull of P₂. -/
lemma closed_hull_convex {n₁ n₂ : ℕ} {P₁ : Fin n₁ → ℝ²} {P₂ : Fin n₂ → ℝ²}
  (h : ∀ i, P₁ i ∈ closed_hull P₂) :
  closed_hull P₁ ⊆ closed_hull P₂ := by
  intro p ⟨β, hβ, hβp⟩
  use fun i ↦ ∑ k, (β k) * (choose (h k) i)
  refine ⟨⟨?_,?_⟩,?_⟩
  · exact fun _ ↦ Fintype.sum_nonneg fun _ ↦ mul_nonneg (hβ.1 _) ((choose_spec (h _)).1.1 _)
  · simp_rw [sum_comm (γ := Fin n₂), ←mul_sum, (choose_spec (h _)).1.2, mul_one]
    exact hβ.2
  · simp_rw [sum_smul, mul_smul, sum_comm (γ := Fin n₂), ←smul_sum, (choose_spec (h _)).2]
    exact hβp


/-
  We define the boundary of a polygon as the elements in the closed hull but not
  in the open hull.
-/

def boundary {n : ℕ} (P : Fin n → ℝ²) : Set ℝ² := (closed_hull P) \ (open_hull P)

lemma boundary_sub_closed {n : ℕ} (P : Fin n → ℝ²) : boundary P ⊆ closed_hull P :=
  Set.diff_subset

lemma boundary_not_in_open {n : ℕ} {P : Fin n → ℝ²} {x : ℝ²} (hx : x ∈ boundary P) :
    x ∉ open_hull P :=  Set.not_mem_of_mem_diff hx

lemma boundary_in_closed {n : ℕ} {P : Fin n → ℝ²} {x : ℝ²} (hx : x ∈ boundary P) :
    x ∈ closed_hull P := Set.mem_of_mem_diff hx
