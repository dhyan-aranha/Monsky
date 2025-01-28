import Mathlib.Tactic
import FormalBook.Appendix
import FormalBook.sperner_pjotr


/-!
# One square and an odd number of triangles
-/

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "Triangle" => Fin 3 → ℝ²
local notation "Segment" => Fin 2 → ℝ²

open BigOperators
open Classical
open Finset

-- First we define the inductive type Color, which will be the target type of the coloring
-- function. The coloring function will take a point in ℝ² and return a color from Color (eg. Red
-- Blue or Green).

inductive Color
| Red
| Green
| Blue

variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀]
variable (v : Valuation ℝ Γ₀)

-- Now we define the coloring function as it appears in the Book.

def coloring : (X : ℝ²) → Color
| X => if v (X 0) < v 1 ∧ v (X 1) < v 1 then Color.Red
  else if v (X 0) < v (X 1) ∧ v (X 1) ≥ v 1 then Color.Green
  else Color.Blue

-- The next three lemmas below reverse the coloring function.
-- Namely, for a given color they return inequalities describing the region with this color.
-- They will be of use in the proof of the lemma on the boundedness of the determinant.

lemma green_region (X : ℝ²) : (coloring v X = Color.Green) → v (X 0) < v (X 1) ∧ v (X 1) ≥ v (1) := by
  intro h
  simp only [coloring, Fin.isValue, map_one, ge_iff_le] at h
  split_ifs at h with h1 h2
  rw [v.map_one]
  exact h2

lemma red_region (X : ℝ²) : (coloring v X = Color.Red) → v (X 0) < v 1 ∧ v (X 1) < v 1 := by
  intro h
  simp only [coloring, Fin.isValue, map_one, ge_iff_le] at h
  split_ifs at h with h1
  rw [v.map_one]
  exact h1

lemma blue_region (X : ℝ²) : (coloring v X = Color.Blue) → v (X 0) ≥ v (1) ∧ v (X 0) ≥ v (X 1) := by
  intro h
  simp only [coloring, Fin.isValue, map_one, ge_iff_le] at h
  split_ifs at h with h1 h2
  rw [v.map_one]
  -- Apply De Morgan's law
  rw [Decidable.not_and_iff_or_not] at h1 h2
  -- Get rid of negations
  rw [not_lt, not_lt] at h1
  rw [not_lt, not_le] at h2
  -- Split h1 into cases
  cases' h1 with p q
  constructor
  · apply p
  · cases' h2 with m n
    apply m
    have q' : v (X 1) ≤ 1 := by
      exact le_of_lt n
    apply le_trans q' p
  -- Split h2 into cases
  cases' h2 with a b
  constructor
  · apply le_trans q a
  · exact a
  -- No more cases left
  rw [← not_lt] at q
  contradiction

-- Record our definition of a rainbow triangle

def rainbow_triangle (T : Fin 3 → ℝ²) : Prop := Function.Surjective (coloring v ∘ T)

-- We need a few inequalities that will be used in the proof of the main lemma.
-- These are just bounds on valuations of terms that appear in the
-- determinant expression that captures the area of a triangle.

lemma valuation_bounds
  (X Y Z : ℝ²)
  (hb : coloring v X = Color.Blue)
  (hg : coloring v Y = Color.Green)
  (hr : coloring v Z = Color.Red) :
  v (X 0 * Y 1) ≥ 1 ∧
  v (X 1 * Z 0) < v (X 0 * Y 1) ∧
  v (Y 0 * Z 1) < v (X 0 * Y 1) ∧
  v (X 0 * Y 1) > v (-(Y 1 * Z 0)) ∧
  v (X 0 * Y 1) > v (-(X 1 * Y 0)) ∧
  v (X 0 * Y 1) > v (-(X 0 * Z 1)) := by

  -- Get rid of all minus signs
  repeat rw [Valuation.map_neg]
  -- Apply multiplicativity of v everywhere
  repeat rw [v.map_mul]

  -- Trivial bounds from the coloring
  have hx0 : v (X 0) ≥ v 1 := (blue_region v X hb).1
  have hy1 : v (Y 1) ≥ v 1 := (green_region v Y hg).2
  have hz0 : v (Z 0) < v 1 := (red_region v Z hr).1
  have hz1 : v (Z 1) < v 1 := (red_region v Z hr).2
  have hxx : v (X 1) ≤ v (X 0) := (blue_region v X hb).2
  have hyy : v (Y 0) < v (Y 1) := (green_region v Y hg).1
  -- Replace v 1 by 1
  simp_all only [map_one]
  -- We won't need the coloring hypotheses anymore
  clear hb hg hr

  -- Non-negativity bounds
  have x0_gt_zero : v (X 0) > 0 := gt_of_ge_of_gt hx0 zero_lt_one
  have y1_gt_zero : v (Y 1) > 0 := gt_of_ge_of_gt hy1 zero_lt_one

  -- v (X 0) * v (Y 1) ≥ 1
  constructor
  exact Right.one_le_mul hx0 hy1

  -- v (X 1) * v (Z 0) < v (X 0) * v (Y 1)
  constructor
  apply mul_lt_mul'
  exact hxx
  exact gt_of_ge_of_gt hy1 hz0
  exact zero_le'
  exact x0_gt_zero

  -- v (Y 0) * v (Z 1) < v (X 0) * v (Y 1)
  constructor
  rw [mul_comm (v (X 0)) (v (Y 1))]
  apply mul_lt_mul''
  exact hyy
  exact gt_of_ge_of_gt hx0 hz1
  exact zero_le'
  exact zero_le'

  -- v (X 0) * v (Y 1) > v (Y 1) * v (Z 0)
  constructor
  rw [mul_comm (v (X 0)) (v (Y 1))]
  apply mul_lt_mul'
  apply refl
  exact gt_of_ge_of_gt hx0 hz0
  exact zero_le'
  exact y1_gt_zero

  -- v (X 0) * v (Y 1) > v (X 1) * v (Y 0)
  constructor
  apply mul_lt_mul' hxx hyy
  apply zero_le'
  exact x0_gt_zero

  -- v (X 0) * v (Y 1) > v (X 0) * v (Z 1)
  apply mul_lt_mul'
  apply refl
  exact gt_of_ge_of_gt hy1 hz1
  exact zero_le'
  exact x0_gt_zero

--The next definition and lemma relate things to matrices more like in the book.
--But they are not needed.

def Color_matrix (X Y Z : ℝ²): Matrix (Fin 3) (Fin 3) ℝ :=
![![X 0, X 1, 1], ![Y 0, Y 1, 1], ![Z 0, Z 1, 1]]

lemma det_of_Color_matrix (X Y Z : ℝ²) :
  Matrix.det (Color_matrix X Y Z) =
   (X 0 * Y 1 + X 1 * Z 0 + Y 0 * Z 1 - Y 1 * Z 0 - X 1 * Y 0 - X 0 * Z 1) := by
rw [Matrix.det_fin_three, Color_matrix]
simp only [Fin.isValue, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
     Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
     Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.tail_cons, Matrix.tail_val',
     Matrix.head_val', Matrix.head_fin_const, mul_one, one_mul]
ring_nf

-- Valuation of a sum of six variables is equal to the valuation of the largest of them
lemma valuation_max
  {A a₁ a₂ a₃ a₄ a₅ : ℝ}
  (h1 : v (A) > v (a₁))
  (h2 : v (A) > v (a₂))
  (h3 : v (A) > v (a₃))
  (h4 : v (A) > v (a₄))
  (h5 : v (A) > v (a₅)) :
  v (A + a₁ + a₂ + a₃ + a₄ + a₅) = v (A) := by
  -- move brackets to the right
  repeat rw [add_assoc]
  -- Now just write the function representing the proof term directly.
  -- exact map_add_eq_of_lt_left v <| map_add_lt v h1 <| map_add_lt v h2 h3
  apply Valuation.map_add_eq_of_lt_left
  repeat (
    apply Valuation.map_add_lt v _ _
    assumption
  )
  assumption

-- This is the first main lemma of Chapter 22

lemma bounded_det
  (X Y Z : ℝ²)
  (hb : coloring v X = Color.Blue)
  (hg : coloring v Y = Color.Green)
  (hr : coloring v Z = Color.Red) :
  v (X 0 * Y 1 + X 1 * Z 0 + Y 0 * Z 1 - Y 1 * Z 0 - X 1 * Y 0 - X 0 * Z 1) ≥ 1 := by
  -- Change minus signs to plus signs
  repeat rw [sub_eq_add_neg]
  -- Establish all required assumptions for the lemma
  rcases (valuation_bounds v X Y Z hb hg hr) with ⟨h0, ⟨h1, ⟨h2, ⟨h3, ⟨h4,h5⟩⟩⟩⟩⟩
  -- Use the above lemma
  rw [valuation_max v h1 h2 h3 h4 h5]
  -- Change the inequality to v (X 0 * Y 1) ≥ 1
  exact h0



-- We now prove that for any line segment in ℝ² contains at most 2 colors.

lemma det_triv_triangle (X Y : ℝ² ) : det (fun | 0 => X | 1 => X | 2 => Y) = 0 := by
  simp [det]

lemma Lhull_equals_Thull (L:Segment) :
closed_hull L = closed_hull (fun | 0 => L 0 | 1 => L 0 | 2 => L 1: Fin 3 → ℝ²) := by

ext x
constructor
intro ⟨α, hα, hαx⟩
use fun | 0 => 0 | 1 => α 0| 2 => α 1
refine ⟨⟨?_,?_⟩, ?_⟩
intro i;  fin_cases i <;> simp [hα.1]
simp [← hα.2, Fin.sum_univ_three];
simp [← hαx, Fin.sum_univ_three];
intro ⟨α, hα, hαx⟩
use fun | 0  => α 0 + α 1| 1 => α 2
refine ⟨⟨?_,?_⟩, ?_⟩
intro i; fin_cases i <;> (simp; linarith [hα.1 0, hα.1 1, hα.1 2])
simp [← hα.2, Fin.sum_univ_three];
simp [← hαx, Fin.sum_univ_three, add_smul]


def b_sign : Fin 6 → ℝ := fun
  | 0 => 1 | 1 => -1 | 2 => -1 | 3 => 1 | 4 => 1 | 5 => -1

def σ : Fin 6 → (Fin 3 → Fin 3) := fun
| 0 => (fun | 0 => 0 | 1 => 1 | 2 => 2)
| 1 => (fun | 0 => 0 | 1 => 2 | 2 => 1)
| 2 => (fun | 0 => 1 | 1 => 0 | 2 => 2)
| 3 => (fun | 0 => 1 | 1 => 2 | 2 => 0)
| 4 => (fun | 0 => 2 | 1 => 0 | 2 => 1)
| 5 => (fun | 0 => 2 | 1 => 1 | 2 => 0)

lemma sign_non_zero : ∀ b, b_sign b ≠ 0 := by
  intro b; fin_cases b <;> simp [b_sign]

lemma fun_in_bijections {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ b, σ b = (fun | 0 => i | 1 => j | 2 => k)  := by
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals (try tauto)
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩
  · exact ⟨5, rfl⟩


lemma det_perm {T : Triangle} (b : Fin 6) :
    det T = (b_sign b) *  det (T ∘ (σ b)) := by
  fin_cases b <;> (simp_all [det, b_sign, σ]; try ring)

lemma det_zero_perm {T : Triangle} (hT  : det T = 0) :
    ∀ i j k, det (fun | 0 => T i | 1 => T j | 2 => T k) = 0 := by
  intro i j k
  by_cases hij : i = j
  · simp [det, hij]
  · by_cases hik : i = k
    · simp [det, hik]; ring
    · by_cases hjk : j = k
      · simp [det, hjk]; ring
      · have ⟨b, hb⟩ := fun_in_bijections hij hik hjk
        rw [det_perm b] at hT
        convert eq_zero_of_ne_zero_of_mul_left_eq_zero (sign_non_zero b) hT
        split <;> simp [hb]

lemma det_zero_01 {T : Triangle} (h01 : T 0 = T 1) :
    det T = 0 := by simp [det, h01]

lemma det_zero_02 {T : Triangle} (h02 : T 0 = T 2) :
    det T = 0 := by simp [det, h02]; ring

lemma det_zero_12 {T : Triangle} (h12 : T 1 = T 2) :
    det T = 0 := by simp [det, h12]; ring

lemma linear_combination_det_middle {n : ℕ} {x z : ℝ²} {P : Fin n → ℝ²} {α : Fin n → ℝ}
    (hα : ∑ i, α i = 1) :
  det (fun | 0 => x | 1 => (∑ i, α i • P i) | 2 => z) =
  ∑ i, (α i * det (fun | 0 => x | 1 => (P i) | 2 => z)) := by
  convert linear_combination_det_last (y := x) (P := P) (x := z) hα using 1
  · convert det_perm 4
    simp [b_sign, σ];
    congr; funext k; fin_cases k <;> rfl
  · congr; ext i; congr 1;
    convert det_perm 4
    simp [b_sign, σ];
    congr; funext k; fin_cases k <;> rfl





lemma linear_combination_det_first {n : ℕ} {y z : ℝ²} {P : Fin n → ℝ²} {α : Fin n → ℝ}
    (hα : ∑ i, α i = 1) :
  det (fun | 0 => (∑ i, α i • P i) | 1 => y | 2 => z) =
  ∑ i, (α i * det (fun | 0 => (P i) | 1 => y | 2 => z)) := by
  convert linear_combination_det_last (y := z) (P := P) (x := y) hα using 1
  · convert det_perm 3
    simp [b_sign, σ];
    congr; funext k; fin_cases k <;> rfl
  · congr; ext i; congr 1;
    convert det_perm 3
    simp [b_sign, σ];
    congr; funext k; fin_cases k <;> rfl


lemma det_0_triangle_imp_triv {T : Triangle} (hT : det T = 0) :
    ∀ x y z, x ∈ closed_hull T → y ∈ closed_hull T → z ∈ closed_hull T →
      det (fun | 0 => x | 1 => y | 2 => z) = 0 := by
  intro x y z ⟨_, ⟨_, hαx⟩ , hx⟩ ⟨_, ⟨_, hαy⟩ , hy⟩ ⟨_, ⟨_, hαz⟩ , hz⟩
  rw [←hx, ← hy, ←hz, linear_combination_det_first hαx]
  simp only [linear_combination_det_middle hαy]
  refine
    Eq.mpr
      (id
        (congrArg (fun x ↦ x = 0)
          (Finset.sum_congr (Eq.refl Finset.univ) fun x a ↦
            congrArg (HMul.hMul (_))
              (Finset.sum_congr (Eq.refl Finset.univ) fun x_1 a ↦
                congrArg (HMul.hMul (_))
                  ((fun x_0 x_1 x_2 ↦
                      (fun x_0 x_1 x_2 ↦ linear_combination_det_last hαz) x_0 x_1 x_2)
                    (T x) (T x_1) T)))))
      ?_ -- this was the breaking simp
  exact
    of_eq_true
      (Eq.trans
        (congrArg (fun x ↦ x = 0)
          (Eq.trans
            (Finset.sum_congr (Eq.refl Finset.univ) fun x a ↦
              Eq.trans
                (congrArg (HMul.hMul (_))
                  (Eq.trans
                    (Finset.sum_congr (Eq.refl Finset.univ) fun x_1 a ↦
                      Eq.trans
                        (congrArg (HMul.hMul (_))
                          (Eq.trans
                            (Finset.sum_congr (Eq.refl Finset.univ) fun x_2 a ↦
                              Eq.trans
                                (congrArg (HMul.hMul (_))
                                  ((fun i j k ↦ det_zero_perm hT i j k) x x_1 x_2))
                                (mul_zero (_)))
                            Finset.sum_const_zero))
                        (mul_zero (_)))
                    Finset.sum_const_zero))
                (mul_zero (_)))
            Finset.sum_const_zero))
        (eq_self 0))









theorem no_Color_lines (L : Segment) {Γ₀ : Type} (locg : LinearOrderedCommGroupWithZero Γ₀)
(v : Valuation ℝ Γ₀) : ∃ c : Color, ∀ P ∈ closed_hull L, coloring v P ≠ c := by

by_contra h
push_neg at h
have hr : ∃ z ∈ closed_hull L , coloring v z = Color.Red := by
  apply h
have hb : ∃ x ∈ closed_hull L , coloring v x = Color.Blue := by
  apply h
have hg : ∃ y ∈ closed_hull L , coloring v y = Color.Green := by
  apply h
rcases hr with ⟨z, hz, hzr⟩
rcases hb with ⟨x, hx, hxb⟩
rcases hg with ⟨y, hy, hyg⟩
let Tseg : Fin 3 → ℝ² := fun | 0 => L 0 | 1 => L 0 | 2 => L 1
have hTseg : det Tseg = 0 := det_triv_triangle (L 0) (L 1)
have rain1: det (fun | 0 => x | 1 => y | 2 => z) = 0 := by
  rw [Lhull_equals_Thull L] at hx hy hz
  exact det_0_triangle_imp_triv hTseg x y z hx hy hz
have vrain1 : v (det (fun | 0 => x | 1 => y | 2 => z)) = v 0 := by
  rw [rain1]
rw [v.map_zero] at vrain1
have rain2: v (det (fun | 0 => x | 1 => y | 2 => z)) ≥ 1 := by
  have h_det : det (fun | 0 => x | 1 => y | 2 => z) =
    (x 0 * y 1 + x 1 * z 0 + y 0 * z 1 - y 1 * z 0 - x 1 * y 0 - x 0 * z 1) := by
    simp [det]
    ring_nf
  rw [h_det]
  apply bounded_det
  exact hxb
  exact hyg
  exact hzr
have contra: v (det (fun | 0 => x | 1 => y | 2 => z)) = 0 ∧
v (det (fun | 0 => x | 1 => y | 2 => z)) ≥ 1 := by
  exact ⟨vrain1, rain2⟩
have ⟨h1, h2⟩ := contra
have h3 : (0 : Γ₀) ≥ 1 := by
  rw [h1] at h2
  exact h2
exact not_le_of_gt (zero_lt_one) h3

-- We show next that the coloring of (0,0) is red, (0,1) is green and (1,0) is blue.

lemma red00 : coloring v ![0,0] = Color.Red := by
  simp [coloring, Fin.isValue, map_one, ge_iff_le]

lemma green01 : coloring v  ![0, 1] = Color.Green := by
  simp [coloring, Fin.isValue, map_one, ge_iff_le]

lemma blue10 : coloring v ![1,0] = Color.Blue := by
  simp [coloring, Fin.isValue, map_one, ge_iff_le]

--TODO: Show that the area of a Color triangle cannot be zero or 1/n for n odd (here we will
-- need the fact that v(1/2) > 1).

lemma get_color_of_rainbow_triangle (T: Fin 3 → ℝ²) (rt: rainbow_triangle v T) (c : Color) :
  ∃ i : Fin 3, coloring v (T i) = c := by
  have h := rt c
  cases' h with i hi
  exact ⟨i, hi⟩


theorem bounded_det_coord_free (T: Triangle)(rt: rainbow_triangle v T) :
v (det T) ≥ 1 := by

have hr: ∃ z : Fin 3, coloring v (T z) = Color.Red := by
  apply get_color_of_rainbow_triangle v T rt Color.Red
have hb: ∃ x : Fin 3, coloring v (T x) = Color.Blue := by
  apply get_color_of_rainbow_triangle v T rt Color.Blue
have hg: ∃ y : Fin 3, coloring v (T y) = Color.Green := by
  apply get_color_of_rainbow_triangle v T rt Color.Green
rcases hr with ⟨z, hz⟩
rcases hb with ⟨x, hx⟩
rcases hg with ⟨y, hy⟩
have hxy : x ≠ y := by
  intro h
  subst h
  simp_all only [reduceCtorEq]
have hxz : x ≠ z := by
  intro h
  aesop
have hyz : y ≠ z := by
  intro h
  aesop
have hT : ∃ b, σ b = (fun | 0 =>  x | 1 =>  y | 2 => z) := by
  apply fun_in_bijections hxy hxz hyz
rcases hT with ⟨b, hb⟩
have h1 : det T = b_sign b * det (T ∘ σ b) := by
  apply det_perm
have h2 : det (T ∘ σ b) =
T x 0 * T y 1 + T x 1 * T z 0 + T y 0 * T z 1 - T y 1 * T z 0 - T x 1 * T y 0 - T x 0 * T z 1 := by
  simp
  rw [det]
  simp [hb]
  ring_nf
have h3 : v (det (T ∘ σ b)) ≥ 1 := by
  rw [h2]
  apply bounded_det v (T x) (T y) (T z) hx hy hz
have h4 : v (b_sign b) = 1 := by
  fin_cases b <;> simp [b_sign, v.map_one]
have h5 : v (det T) = v (b_sign b) * v (det (T ∘ σ b)) := by
  rw [h1, v.map_mul]
rw [h4, one_mul] at h5
rw [h5]
apply h3


theorem no_odd_rainbow_triangle (T : Fin 3 → ℝ²)(rt : rainbow_triangle v T) (vhalf: v (1/2) > 1)
(vodd: ∀ (n : ℕ) (zodd: Odd n), v (1/n) = 1) : ¬ ∃ (n : ℕ) (hodd: Odd n),
|det T| = 2 / n := by

push_neg
intro n hodd
by_contra h
have bound : v (det T) ≥ 1 := by
  apply bounded_det_coord_free v T rt
have val_inv: v (det T ) = v (|det T|) := by
  by_cases
  h : det T ≥ 0
  · simp [abs_of_nonneg h]
  · push_neg at h
    simp [abs_of_neg h]
have v1 : v (det T) = v (2 / n) := by
  rw [val_inv, h]
have v2: v (2 / n) = v (1/2)⁻¹ * v (1/ n) := by
  rw [v.map_div]
  have v3: v 2 = (v (1/2))⁻¹ := by
    rw [← v.map_inv]
    have obv: (2:ℝ)⁻¹ = 1/2 := by
      rw [div_eq_mul_inv]
      rw [one_mul]
    rw [← obv]
    rw [inv_inv]
  rw [v3]
  simp
  rw [← v.map_div]
  rw [← v.map_inv]
  rw [← v.map_mul]
  ring_nf
have v4: v (1/ n) = 1 := by
  apply vodd
  apply hodd
rw [v4] at v2
have bound2: v (2 / n) < 1 := by
  rw [v2]
  rw [mul_one, ← inv_lt_inv₀]
  rw [v.map_inv]
  rw [inv_inv]
  rw [inv_one]
  exact vhalf
  aesop
  rw [← inv_pos, v.map_inv, inv_inv]
  have obv': (0 : Γ₀) < 1 := by
    simp
  rw [gt_iff_lt] at vhalf
  exact lt_trans obv' vhalf
have bound3: v (det T) < 1 := by
  rw [v1]
  apply bound2
exact bound3.not_le bound
