import Mathlib
import Monsky.simplex_basic
import Monsky.segment_triangle
import Monsky.basic_definitions


local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "Triangle" => Fin 3 → ℝ²
local notation "Segment" => Fin 2 → ℝ²


open Classical
open BigOperators
open Finset


noncomputable def segment_set (X : Finset ℝ²) : Finset Segment :=
    Finset.image (fun (a,b) ↦ to_segment a b) ((Finset.product X X).filter (fun (a,b) ↦ a ≠ b))

noncomputable def avoiding_segment_set (X : Finset ℝ²) (A : Set ℝ²) : Finset Segment :=
    (segment_set X).filter (fun L ↦ Disjoint (closed_hull L) (A))

noncomputable def basic_avoiding_segment_set (X : Finset ℝ²) (A : Set ℝ²) : Finset Segment :=
    (avoiding_segment_set X A).filter (fun L ↦ ∀ x ∈ X, x ∉ open_hull L)


inductive Chain : ℝ² → ℝ² → Type
    | basic {u v : ℝ²}  : Chain u v
    | join {u v w : ℝ²} (hCollineair : colin u v w) (C : Chain v w) : Chain u w

noncomputable def to_basic_segments {u v : ℝ²} : Chain u v → Finset Segment
    | Chain.basic              => {to_segment u v}
    | @Chain.join _ w _ _ C    => to_basic_segments C ∪ {to_segment u w}

noncomputable def glue_chains {u v w : ℝ²} (hCollinear : colin u v w) : Chain u v → Chain v w → Chain u w
    | Chain.basic, C      => Chain.join hCollinear C
    | Chain.join h C', C  => Chain.join (interior_collinear (interior_left_trans h.2 hCollinear.2)) (glue_chains (sub_collinear_right hCollinear h.2) C' C)

noncomputable def reverse_chain {u v : ℝ²} : Chain u v → Chain v u
    | Chain.basic           => Chain.basic
    | @Chain.join _ x _ h C => glue_chains (colin_reverse h) (reverse_chain C) (@Chain.basic x u)

noncomputable def chain_to_big_segment {u v : ℝ²} (_ : Chain u v) : Segment := to_segment u v

theorem segment_decomposition (A : Set ℝ²):
    ∀ (X : Finset ℝ²) {S : Segment}, (S ∈ avoiding_segment_set X A) →
    ∃ (C : Chain (S 0) (S 1)), S = chain_to_big_segment C ∧
    (basic_avoiding_segment_set X A).filter (fun s ↦ closed_hull s ⊆ closed_hull S)
    = to_basic_segments C ∪ (to_basic_segments (reverse_chain C)) := by

    sorry



def color : ℝ² → Fin 3 := sorry -- can use the construction using valuations here

def red : Fin 3 := 0
def blue : Fin 3 := 1
def green : Fin 3 := 2


-- The following function determines whether a segment is purple. We want to sum the value
-- of this function over all segments, so we let it take values in ℕ
noncomputable def isPurple : Segment → ℕ :=
    fun S ↦ if ( (color (S 0) = red ∧ color (S 1) = blue) ∨ (color (S 0) = blue ∧ color (S 1) = red)) then 1 else 0

noncomputable def isRainbow : Triangle → ℕ :=
    fun T ↦ if (Function.Surjective (color ∘ T)) then 1 else 0

-- The segment covered by a chain is purple if and only if an odd number of its basic
-- segments are purple.
lemma purple_parity {u v : ℝ²} (C : Chain u v) : ∑ T ∈ to_basic_segments C, isPurple T % 2
    = isPurple (chain_to_big_segment C) := by
  sorry -- can probably be proven by induction


noncomputable def triangulation_points (Δ : Finset Triangle) : Finset ℝ² :=
  Finset.biUnion Δ (fun T ↦ {T 0, T 1, T 2})

-- The union of the interiors of the triangles of a triangulation
noncomputable def triangulation_avoiding_set (Δ : Finset Triangle) : Set ℝ² :=
  {x ∈ {x | ∀ i, 0 < x i ∧ x i < 1} | x ∉ ⋃ (T ∈ Δ), open_hull T}

noncomputable def triangulation_basic_segments (Δ : Finset Triangle) : Finset Segment :=
  basic_avoiding_segment_set (triangulation_points Δ) (triangulation_avoiding_set Δ)

noncomputable def triangulation_all_segments (Δ : Finset Triangle) : Finset Segment :=
  avoiding_segment_set (triangulation_points Δ) (triangulation_avoiding_set Δ)

noncomputable def purple_sum (Δ : Finset Triangle) : ℕ :=
  ∑ (S ∈ triangulation_basic_segments Δ), isPurple S

noncomputable def rainbow_sum (Δ : Finset Triangle) : ℕ :=
  ∑ (T ∈ Δ), isRainbow T

noncomputable def rainbow_triangles (Δ : Finset Triangle) : Finset Triangle :=
  sorry

noncomputable def is_triangulation (Δ : Finset Triangle) : Prop :=
  is_cover {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1} Δ.toSet


theorem segment_sum_odd (Δ : Finset Triangle) (hCovering : is_triangulation Δ) :
    purple_sum Δ % 4 = 2 := by
  sorry


theorem segment_sum_rainbow_triangle (Δ : Finset Triangle) (hCovering : is_triangulation Δ) :
    rainbow_sum Δ = 2 * (rainbow_triangles Δ).card := by
  sorry


theorem rainbow_sum_is_purple_sum (Δ : Finset Triangle) : rainbow_sum Δ = purple_sum Δ := by
  sorry


theorem monsky_rainbow (Δ : Finset Triangle) (hCovering : is_triangulation Δ) :
    ∃ T ∈ Δ, isRainbow T = 1 := by
  sorry
