import Mathlib
import Mathlib.Tactic
import Monsky.segment_triangle

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "Triangle" => Fin 3 → ℝ²
local notation "Segment" => Fin 2 → ℝ²

open Classical
open BigOperators
open Finset


/-
  The closed_hulls of the polygons cover X.
-/
def is_cover {n : ℕ} (X : Set ℝ²) (S : Set (Fin n → ℝ²)) : Prop :=
  (X = ⋃ (P ∈ S), closed_hull P)

/-
  The open_hulls of the polygons do not intersect.
-/
def is_disjoint_polygon_set {n : ℕ} (S : Set (Fin n → ℝ²)) : Prop :=
    (∀ T₁ ∈ S, ∀ T₂ ∈ S, T₁ ≠ T₂ → Disjoint (open_hull T₁) (open_hull T₂))


def is_disjoint_cover {n : ℕ} (X : Set ℝ²) (S : Set (Fin n → ℝ²)) : Prop :=
  is_cover X S ∧ is_disjoint_polygon_set S



/- For now we use this formula as the definition of the area.-/
noncomputable def triangle_area (T : Triangle) : ℝ :=
  abs (det T) / 2

/- -/
def is_equal_area_cover (X : Set ℝ²) (S : Set Triangle) : Prop :=
  is_disjoint_cover X S ∧
  (∃ (area : ℝ), ∀ T, (T ∈ S) → triangle_area T = area)





/- Some theorems involving these definitions. -/

lemma is_cover_sub {n : ℕ} {S : Set (Fin n → ℝ²)} {X : Set ℝ²} (hCover : is_cover X S) :
    ∀ Δ ∈ S, closed_hull Δ ⊆ X := by
  intro _ hΔ
  rw [hCover]
  exact Set.subset_biUnion_of_mem hΔ

lemma is_cover_includes {n : ℕ} {S : Set (Fin n → ℝ²)} {X : Set ℝ²} {x : ℝ²}
    (hCover : is_cover X S) (hx : x ∈ X) : ∃ P ∈ S, x ∈ closed_hull P := by
  unfold is_cover at hCover
  rw [hCover] at hx
  simp_all only [Set.mem_iUnion, exists_prop]


lemma is_cover_open_el_imp_eq {n : ℕ} {S : Set (Fin n → ℝ²)} (hDisj : is_disjoint_polygon_set S)
  {Δ₁ Δ₂ : Fin n → ℝ²} (hΔ₁ : Δ₁ ∈ S) (hΔ₂ : Δ₂ ∈ S) {x : ℝ²} (hx₁ : x ∈ open_hull Δ₁)
  (hx₂ : x ∈ open_hull Δ₂) : Δ₁ = Δ₂ := by
  by_contra hΔ₁₂
  have hx := Set.mem_inter hx₁ hx₂
  rwa [Disjoint.inter_eq (hDisj Δ₁ hΔ₁ Δ₂ hΔ₂ hΔ₁₂)] at hx

lemma cover_mem_side {S : Set Triangle} {X : Set ℝ²} (hCover : is_disjoint_cover X S)
    (hArea : ∀ Δ ∈ S, det Δ ≠ 0) {x : ℝ²} (hx : x ∈ X) (hInt: ∀ Δ ∈ S, x ∉ (open_hull Δ))
    (hv : ∀ i, ∀ Δ ∈ S, x ≠ Δ i) : ∃ Δ ∈ S, ∃ i : Fin 3, x ∈ open_hull (Tside Δ i) := by
  rw [hCover.1, @Set.mem_iUnion₂] at hx
  have ⟨Δ, hΔ, hxΔ⟩ := hx
  have hxBoundary : x ∈ boundary Δ := Set.mem_diff_of_mem hxΔ (hInt Δ hΔ)
  have ⟨i,hi⟩ := el_in_boundary_imp_side (hArea Δ hΔ) hxBoundary ?_
  · exact ⟨Δ,hΔ,i,hi⟩
  · exact fun i ↦ hv i Δ hΔ


lemma no_empty_cover {n : ℕ} {S : Finset (Fin n → ℝ²)} {X : Set ℝ²}
    (hCover : is_cover X S.toSet) (hX : Set.Nonempty X) :
    S.card > 0 := by
  by_contra hS
  apply Set.Nonempty.ne_empty hX
  rw [hCover]
  simp [(by simp_all : S = ∅)]
