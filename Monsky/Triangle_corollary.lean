
--This stuff is copy pasted from another file so I don't have rewrite definitions
import Mathlib
-- import Mathlib.Tactic
-- import Mathlib.Analysis.InnerProductSpace.PiL2
-- import Mathlib.Data.Finset.Basic
-- import Mathlib.Order.Defs
-- import Mathlib.Data.Real.Sign
-- import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
-- import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "Triangle" => Fin 3 → ℝ²
local notation "Segment" => Fin 2 → ℝ²

open Classical
open BigOperators
open Finset


def closed_simplex (n : ℕ)  : Set (Fin n → ℝ) := {α | (∀ i, 0 ≤ α i) ∧ ∑ i, α i = 1}
def open_simplex   (n : ℕ)  : Set (Fin n → ℝ) := {α | (∀ i, 0 < α i) ∧ ∑ i, α i = 1}

lemma closed_simplex_def (n : ℕ ): (closed_simplex n) = {α | (∀ i, 0 ≤ α i) ∧ ∑ i, α i = 1} := by rfl
lemma open_simplex_def (n : ℕ ): (open_simplex n) = {α | (∀ i, 0 < α i) ∧ ∑ i, α i = 1} := by rfl

def closed_hull {n : ℕ} (f : Fin n → ℝ²) : Set ℝ² := (fun α ↦ ∑ i, α i • f i) '' closed_simplex n
def open_hull   {n : ℕ} (f : Fin n → ℝ²) : Set ℝ² := (fun α ↦ ∑ i, α i • f i) '' open_simplex n

lemma closed_hull_def {n : ℕ} (f : Fin n → ℝ²) : closed_hull f = (fun α ↦ ∑ i, α i • f i) '' closed_simplex n := by rfl
lemma open_hull_def {n : ℕ} (f : Fin n → ℝ²) : open_hull f = (fun α ↦ ∑ i, α i • f i) '' open_simplex n := by rfl

noncomputable def triangle_area (T : Triangle) : ℝ :=
  abs (- (T 0 1) * (T 1 0) + (T 0 0) * (T 1 1) + (T 0 1) * (T 2 0) - (T 1 1) * (T 2 0) - (T 0 0) * (T 2 1) + (T 1 0) * (T 2 1)) / 2

def is_cover (X : Set ℝ²) (S : Set Triangle) : Prop :=
  (X = ⋃ (T ∈ S), closed_hull T) ∧
  (Set.PairwiseDisjoint S open_hull)

def is_equal_area_cover (X : Set ℝ²) (S : Set Triangle) : Prop :=
  is_cover X S ∧
  (∃ (area : ℝ), ∀ T, (T ∈ S) → triangle_area T = area)




def v (x y : ℝ) : ℝ² := fun | 0 => x | 1 => y


def Psquare : Fin 4 → ℝ² := (fun | 0 => v 0 0 | 1 => v 1 0 | 2 => v 1 1 | 3 => v 0 1)

def unit_square1 : Set ℝ² := {x : ℝ² | 0 ≤ x 0 ∧ x 0 ≤ 1 ∧ 0 ≤ x 1 ∧ x 1 ≤ 1}
def unit_square : Set ℝ²
  := closed_hull Psquare

def open_unit_square1 : Set ℝ² := {x : ℝ² | 0 < x 0 ∧ x 0 < 1 ∧ 0 < x 1 ∧ x 1 < 1}
def open_unit_square : Set ℝ²
  := open_hull Psquare


@[simp]
lemma v₀_val {x y : ℝ} : (v x y) 0 = x := rfl
@[simp]
lemma v₁_val {x y : ℝ} : (v x y) 1 = y := rfl
-- Copy pasted stuff ends here


--def unit_square : Set ℝ² := {x : ℝ² | 0 ≤ x 0 ∧ x 0 ≤ 1 ∧ 0 ≤ x 1 ∧ x 1 ≤ 1}

/-I think that the most important subpart of this corollary is to show that the volume/area
of the triangles must add up to one. Measure theory tells us that the area of a disjoint union is
the sum of the areas. However, in order to apply this, we first need to that both that the `true' area
of a triangle corresponds to the version of area in Monsky's theorem. Secondly, we need that the
sets we work with are measurable.

To show that the true area is indeed the determinant area, we start by proving that the open hull of the
 `unit triangle' has volume 1/2, where this triangle is given by
((0,0),(1,0)(0,1)). From this we calculate the volumes of the other triangles, using the fact that
the volume of an object is invariant under translation and scale with the determinant of a linear
transformation.

For the measurability we do something similar: we show that the unit triangle is measurable, then we
show that any nondegenerate triangle is a preimage of a measurable function of the open hull of
the unit triangle. For degenerate triangles, we use that they have measure zero, and are thus
null-measurable, which is a weaker statement but sufficient for our result (They are actually measurable
but this is probably quite annoying to show)-/


--We start with the definition of the unit triangle

def unit_triangle : Triangle := fun | 0 => (v 0 0) | 1 => (v 1 0) | 2 => (v 0 1)
lemma unit_triangle_def : unit_triangle = fun | 0 => (v 0 0) | 1 => (v 1 0) | 2 => (v 0 1) := by rfl

--Then we have the statement that the open hull of the unit triangle has the right area, plus we add the statement that it is measurable
theorem volume_open_unit_triangle : (MeasureTheory.volume (open_hull unit_triangle)) = 1/2 := by sorry
theorem volume_open_unit_triangle1 : (MeasureTheory.volume (open_hull unit_triangle)).toReal = 1/2 := by sorry

theorem measurable_unit_triangle : MeasurableSet (open_hull unit_triangle) := by sorry

-- Now that we have this, we want to show that the areas can be nicely transformed, for which we use tthis theorem
theorem area_lin_map ( L : ℝ² →ₗ[ℝ ]  ℝ²) (A : Set ℝ²) : MeasureTheory.volume (Set.image L A) = (ENNReal.ofReal (abs ( LinearMap.det L ))) * (MeasureTheory.volume (A)) := by
  exact MeasureTheory.Measure.addHaar_image_linearMap MeasureTheory.volume L A

--We have something similar for translations, but we first have to give a definition of a translation :)
def translation (a : ℝ²) : (ℝ² → ℝ²) := fun x ↦ x + a

theorem area_translation (a : ℝ²)(A : Set ℝ²) :  MeasureTheory.volume (Set.image (translation a) A) = MeasureTheory.volume (A) :=   by
  unfold translation
  simp

-- If we want to use these two theorems we need the proof that a generic triangle is given by a linear transform and the translation. For this we show that a linear transformation commutes with the open hull operation, in which we use the following lemma
lemma lincom_commutes ( L : ℝ² →ₗ[ℝ ]  ℝ²){n : ℕ}(a : Fin n → ℝ)(f : Fin n → ℝ²): ∑ i : Fin n, a i • L (f i)  =L (∑ i : Fin n, (a i) • (f i)) := by
  rw[  map_sum L (fun i ↦  a i • f i) univ]
  apply Fintype.sum_congr
  exact fun i ↦ Eq.symm (LinearMap.CompatibleSMul.map_smul L (a i) (f i))

theorem open_hull_lin_trans ( L : ℝ² →ₗ[ℝ ]  ℝ²){n : ℕ }(f : (Fin n → ℝ²)) : open_hull (L ∘ f ) = Set.image L (open_hull f) := by
  rw[open_hull_def, open_hull_def, ← Set.image_comp] -- for some reason repeat rw does not work here
  ext x
  constructor
  · rintro ⟨ a ,h1 , h2⟩
    dsimp at h2
    use a
    constructor
    · exact h1
    · have h3 : (⇑L ∘ fun a ↦ ∑ i : Fin n, a i • f i) a = L  (∑ i : Fin n, a i • f i) :=by rfl
      rw[ h3, ← lincom_commutes L a f, h2]
  · rintro ⟨ a ,h1 , h2⟩
    dsimp at h2
    use a
    constructor
    · exact h1
    · have h3 : (fun α ↦ ∑ i : Fin n, α i • (⇑L ∘ f) i) a =  (∑ i : Fin n, a i • L (f i)) := by rfl
      rw[ h3, lincom_commutes L a f, h2]

--Now also for the closed version, whose proof is almost identical
theorem closed_hull_lin_trans ( L : ℝ² →ₗ[ℝ ]  ℝ²){n : ℕ }(f : (Fin n → ℝ²)) : closed_hull (L ∘ f ) = Set.image L (closed_hull f) := by
  rw[closed_hull_def, closed_hull_def, ← Set.image_comp] -- for some reason repeat rw does not work here
  ext x
  constructor
  · rintro ⟨ a ,h1 , h2⟩
    dsimp at h2
    use a
    constructor
    · exact h1
    · have h3 : (⇑L ∘ fun a ↦ ∑ i : Fin n, a i • f i) a = L  (∑ i : Fin n, a i • f i) :=by rfl
      rw[ h3, ← lincom_commutes L a f, h2]
  · rintro ⟨ a ,h1 , h2⟩
    dsimp at h2
    use a
    constructor
    · exact h1
    · have h3 : (fun α ↦ ∑ i : Fin n, α i • (⇑L ∘ f) i) a =  (∑ i : Fin n, a i • L (f i)) := by rfl
      rw[ h3, lincom_commutes L a f, h2]

--Again we have a similar lemma
lemma aux_for_translation {n : ℕ }{f: Fin n → ℝ²}{a : Fin n → ℝ }{b : ℝ² }(h1 : a ∈ open_simplex n):   ∑ i : Fin n, a i • (f i + b) =  ∑ i : Fin n, a i • f i + b := by
  rcases h1 with ⟨_, h3⟩
  have h4: b = ∑ i : Fin n, a i • b
  rw[← sum_smul, h3, one_smul]
  nth_rewrite 2 [h4]
  rw[← sum_add_distrib]
  apply Fintype.sum_congr
  exact fun i ↦ DistribSMul.smul_add (a i) (f i) b

--Most of the proof of open_hull_lin_trans now gets copied
theorem translation_commutes {n : ℕ }(f : (Fin n → ℝ²)) (b : ℝ²) : open_hull ( (translation b) ∘ f) = Set.image (translation b) (open_hull f) := by
  have htrans : translation b = fun x ↦ x + b := by rfl
  rw[open_hull_def, open_hull_def, ← Set.image_comp]
  rw[htrans] at *
  ext x
  constructor
  · rintro ⟨ a ,h1 , h2⟩
    dsimp at h2
    exact ⟨ a, h1, by dsimp ; rwa[← aux_for_translation h1]⟩
  · rintro ⟨ a ,h1 , h2⟩
    dsimp at h2
    exact ⟨ a, h1, by dsimp ; rwa[ aux_for_translation h1]⟩

-- And the version for the closed hull, that needs an adapted different lemma
theorem aux_for_translation_closed {n : ℕ }{f: Fin n → ℝ²}{a : Fin n → ℝ }{b : ℝ² }(h1 : a ∈ closed_simplex n):   ∑ i : Fin n, a i • (f i + b) =  ∑ i : Fin n, a i • f i + b := by
  rcases h1 with ⟨_, h3⟩
  have h4: b = ∑ i : Fin n, a i • b
  rw[← sum_smul, h3, one_smul]
  nth_rewrite 2 [h4]
  rw[← sum_add_distrib]
  apply Fintype.sum_congr
  exact fun i ↦ DistribSMul.smul_add (a i) (f i) b

theorem translation_commutes_closed {n : ℕ }(f : (Fin n → ℝ²)) (b : ℝ²) : closed_hull ( (translation b) ∘ f) = Set.image (translation b) (closed_hull f) := by
  have htrans : translation b = fun x ↦ x + b := by rfl
  rw[closed_hull_def, closed_hull_def, ← Set.image_comp]
  rw[htrans] at *
  ext x
  constructor
  · rintro ⟨ a ,h1 , h2⟩
    dsimp at h2
    exact ⟨ a, h1, by dsimp ; rwa[← aux_for_translation_closed h1]⟩
  · rintro ⟨ a ,h1 , h2⟩
    dsimp at h2
    exact ⟨ a, h1, by dsimp ; rwa[ aux_for_translation_closed h1]⟩

-- Now we explicitly give the translation and linear map that so that the unit triangle gets mapped unto the triangle
--First, we make explicit that our basis is the standard basis
noncomputable def our_basis : Basis (Fin 2) ℝ ℝ² :=  PiLp.basisFun 2 ℝ (Fin 2)
noncomputable def our_basis_ortho : OrthonormalBasis (Fin 2) ℝ ℝ² :=   EuclideanSpace.basisFun (Fin 2) ℝ

--This map tells us how the basis elements should be mapped
noncomputable def basis_transform (T: Triangle ) : (Fin 2 → ℝ²) := (fun | 0 => (T 1 - T 0) | 1 => (T 2 -T 0))

--And then Lean knows how to make a linear map from this
noncomputable def linear_transform (T : Triangle) := our_basis.constr ℝ (basis_transform T)

--This is our translation
def triangle_translation (T : Triangle) := translation (T 0)

-- And then some API which I am actually not sure is required
theorem our_basis_def : our_basis = PiLp.basisFun 2 ℝ (Fin 2) := by rfl
theorem basis_transform_def (T: Triangle) : basis_transform T =  (fun | 0 => (T 1 - T 0) | 1 => (T 2 -T 0)) := by rfl
theorem linear_transform_def (T : Triangle) : linear_transform T =  our_basis.constr ℝ (basis_transform T) := by rfl
theorem triangle_translation_def (T : Triangle ): triangle_translation T =  translation (T 0) := by rfl

--This theorem tells us that these maps indeed do the trick, for which we use translation_commutes and open_hull_lin_trans to show that it is sufficient to show that the points of the unit triangle gets mapped to the triangle (instead of the entirety of the open hull)
theorem unit_triangle_to_triangle (T : Triangle): Set.image (triangle_translation T) (Set.image (linear_transform T) (open_hull unit_triangle)) = open_hull T:= by
  have h1 : triangle_translation T = translation (T 0) := by rfl
  let f : (Fin 3 → ℝ²) := fun | 0 => (v 0 0) | 1 => (v 1 0) | 2 => (v 0 1)
  have hunit_triangle : unit_triangle = f :=by rfl
  rw[hunit_triangle, h1]
  have h2 : open_hull (linear_transform T ∘ f )= ⇑(linear_transform T) '' open_hull f
  exact open_hull_lin_trans (linear_transform T) f
  rw[← h2]
  --rw[← open_hull_lin_trans (linear_transform T) f] Why doesnt this work!??
  rw[← translation_commutes]
  apply congrArg
  --This part of the proof says that the linear transformation and translation of the unit triangle give the triangle we want
  ext i j
  fin_cases i <;> fin_cases j <;>  simp[translation, linear_transform, basis_transform,f, our_basis]

--We are allmost ready to show that the volume of triangles scale the way we want them to, but we just need a silly lemma first
lemma half_is_half : (2⁻¹ : ENNReal) = ENNReal.ofReal (2⁻¹ : ℝ ) := by
  have h1: (2:ℝ)  > 0
  norm_num
  rw[ENNReal.ofReal_inv_of_pos h1]
  norm_num

--One version of this statement in Real numbers, the other in ENNReal, in terms of proof efficiency these probably should not be completely seperate proofs
theorem volume_open_triangle ( T : Triangle ) : (MeasureTheory.volume (open_hull T)).toReal =  (triangle_area (T : Triangle)) := by
  rw[← unit_triangle_to_triangle T ,triangle_translation_def]
  rw[ area_translation, area_lin_map, volume_open_unit_triangle]
  rw[← Matrix.toLin_toMatrix our_basis our_basis  ( linear_transform T ) ]
  rw[LinearMap.det_toLin our_basis ((LinearMap.toMatrix our_basis our_basis) (linear_transform T))]
  rw[Matrix.det_fin_two]
  rw[linear_transform_def, basis_transform_def, our_basis_def, triangle_area ]
  repeat rw[LinearMap.toMatrix_apply]
  simp

  ring_nf

theorem volume_open_triangle1 ( T : Triangle ) : (MeasureTheory.volume (open_hull T)) =  ENNReal.ofReal (triangle_area (T : Triangle)) := by
  rw[← unit_triangle_to_triangle T ,triangle_translation_def]
  rw[ area_translation, area_lin_map, volume_open_unit_triangle]
  rw[← Matrix.toLin_toMatrix our_basis our_basis  ( linear_transform T ) ]
  rw[LinearMap.det_toLin our_basis ((LinearMap.toMatrix our_basis our_basis) (linear_transform T))]
  rw[Matrix.det_fin_two]
  rw[linear_transform_def, basis_transform_def, our_basis_def, triangle_area ]
  repeat rw[LinearMap.toMatrix_apply]

  simp
  rw[half_is_half]
  have h2 : ((0:ℝ) ≤ 2⁻¹ )
  norm_num
  rw[← ENNReal.ofReal_mul' h2]
  ring_nf

--Now that we know the volume of open triangles, we also want to know the area of segments. For this we have a similar strategy. We first take a unit segment, and show it is a subset of the y axis which as hhas measure zero
def unit_segment : Segment := fun | 0 => (v 0 0) | 1 => (v 1 0)
def y_axis : Submodule ℝ ℝ² := Submodule.span ℝ (Set.range unit_segment )

--And some possibly unnecessary API
lemma unit_segment_def : unit_segment = fun | 0 => (v 0 0) | 1 => (v 1 0)  := by rfl
theorem y_axis_def :  y_axis = Submodule.span ℝ (Set.range unit_segment ) := by rfl

--The proof this closed hull of the unit segment is contained in the y-axis
theorem closed_unit_segment_subset : closed_hull unit_segment ⊆ y_axis := by
  intro x
  rintro ⟨  a ,⟨ _,_⟩  , h2⟩
  rw[y_axis]
  --this is to get rid of the annoying coercion
  have h :(x ∈ (Submodule.span ℝ (Set.range unit_segment))) →  x ∈ ↑(Submodule.span ℝ (Set.range unit_segment))
  intro h1
  exact h1
  apply h

  rw[ mem_span_range_iff_exists_fun]
  use a

--And the conclusion it then must have measure zero, which can probably be a lot cleaner
theorem volume_closed_unit_segment : MeasureTheory.volume (closed_hull unit_segment) = 0 := by
  apply MeasureTheory.measure_mono_null (closed_unit_segment_subset )
  apply MeasureTheory.Measure.addHaar_submodule
  intro h
  have h3 : (fun | 0 => 0 | 1 => 1) ∉ y_axis
  intro h1
  rw[y_axis] at h1
  rw[ mem_span_range_iff_exists_fun] at h1
  cases' h1 with c h1
  rw[Fin.sum_univ_two, unit_segment_def] at h1
  simp at h1
  apply congrFun at h1
  specialize h1 1
  dsimp at h1
  have h2 : c 0 * 0 + c 1 * 0 = 0
  linarith
  rw[h2] at h1
  apply zero_ne_one at h1
  exact h1
  rw[h] at h3
  apply h3
  trivial

--Now for segments we also need linear maps and translations
noncomputable def basis_transform_segment (L: Segment ) : (Fin 2 → ℝ²) := (fun | 0 => (L 1 - L 0) | 1 => 0)
noncomputable def linear_transform_segment (L : Segment) := our_basis.constr ℝ (basis_transform_segment L)
def segment_translation (L : Segment) := translation (L 0)

--Some API
theorem basis_transform_segment_def (L : Segment)  : basis_transform_segment L =  (fun | 0 => (L 1 - L 0) | 1 => 0) := by rfl
theorem linear_transform_segment_def (L : Segment) : linear_transform_segment L =  our_basis.constr ℝ (basis_transform_segment L) := by rfl
theorem segment_translation_def (L : Segment) : segment_translation L =  translation (L 0) := by rfl

--Proving these transformations are the right ones
theorem unit_segment_to_segment ( L : Segment) : Set.image (segment_translation L) (Set.image (linear_transform_segment L) (closed_hull unit_segment)) = closed_hull L := by
  have h1 : segment_translation L = translation (L 0) := by rfl
  let f : (Fin 2 → ℝ²) := fun | 0 => (v 0 0) | 1 => (v 1 0)
  have hunit_segment : unit_segment = f :=by rfl
  rw[hunit_segment, h1]
  have h2 : closed_hull (linear_transform_segment L ∘ f )= ⇑(linear_transform_segment L) '' closed_hull f
  exact closed_hull_lin_trans (linear_transform_segment L) f
  rw[← h2]
  --rw[← open_hull_lin_trans (linear_transform T) f] Why doesnt this work!??
  rw[← translation_commutes_closed]
  apply congrArg
  --This part of the proof says that the linear transformation and translation of the unit triangle give the triangle we want
  ext i j
  fin_cases i <;> fin_cases j <;> simp[translation, linear_transform_segment, basis_transform_segment,f, our_basis]

--Proving they all have zero area
theorem volume_closed_segment( L : Segment ) : (MeasureTheory.volume (closed_hull L)) = 0 := by
  rw[←  unit_segment_to_segment L ,segment_translation_def]
  rw[ area_translation, area_lin_map, volume_closed_unit_segment]
  rw[← Matrix.toLin_toMatrix our_basis our_basis  ( linear_transform_segment L ) ]
  rw[LinearMap.det_toLin our_basis ((LinearMap.toMatrix our_basis our_basis) (linear_transform_segment L))]
  rw[Matrix.det_fin_two]
  rw[linear_transform_segment_def, basis_transform_segment_def, our_basis_def ]
  repeat rw[LinearMap.toMatrix_apply]
  simp


--We also in the end need that the unit square has volume 1. The unit square is equal to the square spanned by the basis vectors, which Lean knows has volume 1. This is proved here, although the prove is not finished
theorem box_equal_to_pare : parallelepiped our_basis_ortho = unit_square := by
  ext x
  constructor
  · rw[mem_parallelepiped_iff , unit_square, closed_hull]
    rintro ⟨ t, ⟨ ⟨ h0,h1⟩ , h2⟩⟩
    use (fun | 0 => 1 + max 0 (t 0 + t 1 -1) - t 0 - t 1 | 1  => t 0 - ( max 0 (t 0 + t 1 -1)) | 2 =>  max 0 (t 0 + t 1 -1) | 3 => t 1 - ( max 0 (t 0 + t 1 -1)))
    constructor
    · constructor
      . intro i
        fin_cases i <;> simp
        sorry
        sorry
        sorry

      · rw[Fin.sum_univ_four]
        simp
        ring
    · simp
      rw[h2, Fin.sum_univ_two, Fin.sum_univ_four]
      simp[Psquare, our_basis_ortho]
      ext i
      fin_cases i <;> simp

  · rw[mem_parallelepiped_iff , unit_square, closed_hull]
    rintro ⟨ a ,⟨ h11,h12⟩  , h2⟩
    use (fun | 0 => a 1 + a 2 | 1 => a 3 + a 2  )
    constructor
    · simp

      sorry
    · rw[← h2]
      simp[our_basis_ortho, Fin.sum_univ_four , Psquare]
      ext i
      fin_cases i <;> simp
      linarith

theorem volume_box : (MeasureTheory.volume (unit_square)).toReal = 1 := by
  rw[← box_equal_to_pare]
  rw[OrthonormalBasis.volume_parallelepiped our_basis_ortho]
  rfl

--Now that we have calculated the volume, we move on to showing all this stuff is (null)measurable. For this we distinguish between the case where the triangles are degenerate or not

--this is not very clean, also because this theorem is also proved earlier when translating the triangles
theorem det_of_triangle_transform ( T : Triangle): |LinearMap.det (linear_transform T)|/2 = triangle_area T := by
  rw[← Matrix.toLin_toMatrix our_basis our_basis  ( linear_transform T ) ]
  rw[LinearMap.det_toLin our_basis ((LinearMap.toMatrix our_basis our_basis) (linear_transform T))]
  rw[Matrix.det_fin_two]
  rw[linear_transform_def, basis_transform_def, our_basis_def ,triangle_area]
  repeat rw[LinearMap.toMatrix_apply]
  simp
  ring_nf

--The proof that the linear map corresponding to a nondegenerate triangle has nonzero determinant
theorem nondegen_triangle_lin_inv ( T : Triangle) (h : triangle_area T ≠ 0) : LinearMap.det (linear_transform T) ≠ 0 := by
  intro h2
  rw[← det_of_triangle_transform] at h
  rw[h2] at h
  simp at h

-- This is the same linear transformation but now in the type of invertible map
noncomputable def bij_linear_transform ( T : Triangle) (h : triangle_area T ≠ 0) := (LinearMap.equivOfDetNeZero (linear_transform T) (nondegen_triangle_lin_inv T h))

--These statements are basically a consequence of that the linear map, but are used in the later proof
lemma linear_transform_bij ( T : Triangle) (h : triangle_area T ≠ 0) : Function.Bijective (linear_transform T ) := by
  exact LinearEquiv.bijective (bij_linear_transform ( T : Triangle) (h : triangle_area T ≠ 0))

lemma linear_transform_bij_left_inf ( T : Triangle) (h : triangle_area T ≠ 0) : Function.LeftInverse (linear_transform T) ((bij_linear_transform T h).symm) := by
  exact ((bij_linear_transform T h).symm).left_inv

--This is the inverse of the original triangle translation map, and the proof that are necessary to work with it
def inv_triangle_translation (T : Triangle) := translation ( - T 0)

lemma translation_bijective (a : ℝ² ): Function.Bijective (translation a) := by
  unfold translation
  constructor
  · intro x y
    simp
  · intro x
    use x - a
    norm_num

lemma triangle_translation_bijective (T : Triangle) : Function.Bijective (triangle_translation T) := by
  unfold triangle_translation
  exact translation_bijective (T 0)

lemma inv_translation_left ( T : Triangle) :  Function.LeftInverse (triangle_translation T) (inv_triangle_translation T) := by
  intro x
  rw[inv_triangle_translation, triangle_translation, translation,translation]
  norm_num

--This is unit_triangle_to_triangle in its pre-image form
theorem pre_unit_triangle_to_triangle (T : Triangle) (h : triangle_area T ≠ 0):  (linear_transform T) ⁻¹' ( (triangle_translation T)⁻¹'(open_hull T)) = open_hull unit_triangle:= by
  rw[Set.preimage_eq_iff_eq_image  (linear_transform_bij  T  h )]
  rw[Set.preimage_eq_iff_eq_image (triangle_translation_bijective T)]
  symm
  exact unit_triangle_to_triangle (T : Triangle)

--We can use then use the previous to show that the open hull of the triangle is a preimage of the open unit triangle
theorem pre_triangle_to_unit_triangle (T : Triangle) (h : triangle_area T ≠ 0) :(inv_triangle_translation T)⁻¹'  ((bij_linear_transform T h).symm⁻¹' (open_hull unit_triangle)) = open_hull T := by
  rw[← pre_unit_triangle_to_triangle T h]
  rw[Function.LeftInverse.preimage_preimage (linear_transform_bij_left_inf T h) (triangle_translation T ⁻¹' open_hull T)]
  rw[Function.LeftInverse.preimage_preimage (inv_translation_left T) ]

--In order to actually use this, we need that all these maps are measurable
theorem meas_lin_map ( L : ℝ² →ₗ[ℝ ]  ℝ²) : Measurable L := by
  let K := LinearMap.toContinuousLinearMap L
  have h := ContinuousLinearMap.measurable K
  exact h

theorem meas_translation ( a : ℝ²) : Measurable (translation a) := by
  unfold translation
  exact Measurable.add_const (fun ⦃t⦄ a ↦ a) a

lemma meas_inv_triangle_translation(T : Triangle) : Measurable (inv_triangle_translation T) := by
  unfold inv_triangle_translation
  exact meas_translation (- T 0)

--Then we can show that nondegenerate triangles are measurable
theorem nondegen_triangle_meas ( T : Triangle) (h : triangle_area T ≠ 0) : MeasurableSet (open_hull T) := by
  rw[← pre_triangle_to_unit_triangle T h]
  have h1 : MeasurableSet ((bij_linear_transform T h).symm ⁻¹' open_hull unit_triangle) := measurableSet_preimage (meas_lin_map (bij_linear_transform T h).symm) measurable_unit_triangle
  exact measurableSet_preimage (meas_inv_triangle_translation T) h1

--As any set of measure zero is null measurable, we have then that all triangles are null measurable
theorem null_meas_triangle (T : Triangle) : MeasureTheory.NullMeasurableSet (open_hull T) := by
  by_cases h : triangle_area T > 0
  · have h1 : triangle_area T ≠  0
    exact Ne.symm (ne_of_lt h)
    exact MeasurableSet.nullMeasurableSet (nondegen_triangle_meas T h1)
  · simp at h
    apply ENNReal.zero_eq_ofReal.mpr at h
    rw[← volume_open_triangle1 T] at h
    apply MeasureTheory.NullMeasurableSet.of_null
    symm
    exact h

--Now that we have also have measurability we can start the real work
--We define the edge points of the triangle
def edges_triangle (T : Triangle) : (Fin 3 → Segment ) := fun | 0 => (fun | 0 => T 0 | 1 => T 1) | 1 => (fun | 0 => T 1 | 1 => T 2) | 2 => (fun | 0 => T 2 | 1 => T 0)

--And show that the closed hull of these edges together with an open triangle makes a closed triangle
def all_edges_triangle_hull (T : Triangle) := closed_hull (edges_triangle T 0) ∪ closed_hull (edges_triangle T 1) ∪ closed_hull (edges_triangle T 2)

--This stuff has already be done by Pjotr, but only for nondegenerate triangles ( I think), so maybe this means it has to be shown again anyhow? I am not sure
theorem closed_triangle_is_union (T : Triangle) : closed_hull T = open_hull T ∪ all_edges_triangle_hull T := by
  sorry

--This is useful lemma
lemma volume_zero ( A B: Set ℝ² ) (h : MeasureTheory.volume B = 0) : MeasureTheory.volume (A ∪ B) = MeasureTheory.volume A := by
  symm
  apply MeasureTheory.measure_eq_measure_of_null_diff
  exact Set.subset_union_left
  have h1 : ((A ∪ B) \ A) ⊆ B
  exact Set.diff_subset_iff.mpr fun ⦃a⦄ a ↦ a
  exact MeasureTheory.measure_mono_null h1 h

--This shows that the boundary (but not Pjotrs boundary) of a triangle has measure zero
theorem all_edges_triangle_hull_area (T: Triangle) : MeasureTheory.volume (all_edges_triangle_hull T) = 0:= by
  unfold all_edges_triangle_hull
  repeat rw[volume_zero]
  exact volume_closed_segment (edges_triangle T 0)
  exact volume_closed_segment (edges_triangle T 1)
  exact volume_closed_segment (edges_triangle T 2)

--This shows that all boundaries combined also have measure zero. This proof is a lot uglier then I would like it to be, it might be due to a lack of understanding of sums and unions....
theorem union_of_edges_zero_vol (S : Finset Triangle) : MeasureTheory.volume ( ⋃ (T ∈ S) , all_edges_triangle_hull T ) = 0 := by
  let f := Set.restrict S all_edges_triangle_hull
  have h : ∀ (i : S), MeasureTheory.NullMeasurableSet (f i)
  · intro T
    exact MeasureTheory.NullMeasurableSet.of_null (all_edges_triangle_hull_area T)
  have hd : Pairwise (Function.onFun (MeasureTheory.AEDisjoint MeasureTheory.volume) f)
  · intro i j _
    rw[Function.onFun_apply]
    have h2 : S.restrict all_edges_triangle_hull i ∩ S.restrict all_edges_triangle_hull j ⊆ S.restrict all_edges_triangle_hull i := Set.inter_subset_left
    apply MeasureTheory.measure_mono_null h2 (all_edges_triangle_hull_area i)
  have h4 :  ⋃ T ∈ S, all_edges_triangle_hull T= (⋃ i, (Finset.toSet S).restrict all_edges_triangle_hull i)
  exact Eq.symm (Set.iUnion_subtype (Membership.mem S) (S.restrict all_edges_triangle_hull))
  rw[h4]
  rw[MeasureTheory.measure_iUnion₀ hd h]
  have h5 : (fun x ↦ MeasureTheory.volume (f x))= (fun x ↦ 0)
  · ext x
    unfold f
    exact all_edges_triangle_hull_area x
  rw[h5]
  exact ENNReal.tsum_eq_zero.mpr (congrFun rfl)

--

-- theorem null_measurable_segment (L : Segment): MeasureTheory.NullMeasurableSet (closed_hull L) := by
--   exact MeasureTheory.NullMeasurableSet.of_null (volume_closed_segment L)
  --MeasureTheory.NullMeasurableSet.of_null

--MeasureTheory.measure_iUnion₀
-- def point0 : (Fin 2 → ℝ ) := fun | 0 => 0 | 1 => 0
-- def point1 : (Fin 2 → ℝ ) := fun | 0 => 1 | 1 => 0

-- theorem closed_unit_segment_is_box : (closed_hull unit_segment) = Set.Icc point0 point1 := by
--   have hunit_segment : unit_segment = fun | 0 => (v 0 0) | 1 => (v 1 0) := by rfl
--   have hp0 : point0 = fun | 0 => 0 | 1 => 0 := by rfl
--   have hp1 : point1 = fun | 0 => 1 | 1 => 0 := by rfl
--   ext x
--   constructor
--   · rintro ⟨ a ,⟨ h1,h3⟩  , h2⟩
--     rw[hunit_segment] at h2
--     simp at *
--     rw[← h2]
--     constructor
--     · intro i
--       rw[hp0]
--       fin_cases i <;> dsimp <;> linarith[h1 0, h1 1]
--     · intro i -- this part is directly copied except there is hp1 instead of hp0
--       rw[hp1]
--       fin_cases i <;> dsimp <;> linarith[h1 0, h1 1]
--   · rintro ⟨ h1, h2⟩
--     use (fun | 0 =>  (1 - x 0) | 1 => x 0)
--     rw[hp0,hp1] at *
--     dsimp at *
--     constructor
--     · specialize h1 0
--       specialize h2 0
--       dsimp at *
--       constructor
--       · intro i
--         fin_cases i <;> dsimp <;> linarith[h1, h1]
--       · simp
--     · ext i
--       rw[hunit_segment]
--       fin_cases i
--       · simp
--       · simp
--         specialize h1 1
--         specialize h2 1
--         dsimp at *
--         linarith



--#check MeasureTheory.MeasurePreserving.map_eq (EuclideanSpace.volume_preserving_measurableEquiv (Fin 2))
--#check EuclideanSpace.volume_preserving_measurableEquiv
--#check Set.Icc point0 point1



-- theorem volume_closed_unit_segment : (MeasureTheory.volume (closed_hull unit_segment)).toReal = 0 := by
--   -- This first part is essentially showing 0 = (MeasureTheory.volume (Set.Icc point0 point1)).toReal
--   have h0 : ∏ i : (Fin 2), (point1 i - point0 i) = 0
--   rw[ Fin.prod_univ_two]
--   unfold point0 point1
--   linarith
--   rw[ ← h0]
--   have h1: point0 ≤ point1
--   intro i
--   fin_cases i <;> dsimp <;> rw[ point0, point1] ; linarith
--   rw[ ← Real.volume_Icc_pi_toReal h1]
--   -- Now I try to show (MeasureTheory.volume (closed_hull unit_segment)).toReal = (MeasureTheory.volume (Set.Icc point0 point1)).toReal
--   -- But the left-hand side Measuretheory.volume is not the same as the right-hand side
--   have h2 : MeasureTheory.Measure.map (⇑(EuclideanSpace.measurableEquiv (Fin 2))) MeasureTheory.volume  (Set.Icc point0 point1) = MeasureTheory.volume (Set.Icc point0 point1)
--   rw[ MeasureTheory.MeasurePreserving.map_eq (EuclideanSpace.volume_preserving_measurableEquiv (Fin 2))]
--   rw[ ← h2]
--   rw[ closed_unit_segment_is_box] --This is the theorem stating closed_hull unit_segment = Set.Icc point0 point1
--   sorry
--   --rw[ MeasureTheory.MeasurePreserving.map_eq (EuclideanSpace.volume_preserving_measurableEquiv (Fin 2))]


-- theorem segment_subset_affine_space (L : Segment) : closed_hull L ⊆ line[ℝ, (L 0), (L 1)] := by
--   intro x
--   rintro ⟨  a ,⟨ h1,h3⟩  , h2⟩
--   use L 0
--   constructor
--   · left
--     rfl
--   · use a 1 • (L 1 - L 0)
--     constructor
--     · apply mem_vectorSpan_pair_rev.mpr
--       use a 1
--       rfl
--     · dsimp at * -- I thought this could done by some linarith or simp, but it seems I have to do it by hand
--       rw[Fin.sum_univ_two] at h2 h3
--       have h4 : L 0 = (1: ℝ ) • L 0 := Eq.symm (MulAction.one_smul (L 0))
--       nth_rewrite 2 [h4]
--       rw[← h3,← h2 ,smul_sub (a 1) (L 1) (L 0), Module.add_smul (a 0) (a 1) (L 0)]
--       have h5: a 1 •  L 1 - a 1 • L 0 = a 1 • L 1 + (- a 1) • L 0
--       simp
--       exact rfl
--       rw[h5]
--       have h6: a 1 • L 1 + -a 1 • L 0 + (a 0 • L 0 + a 1 • L 0) = a 1 • L 1 + (-a 1 • L 0 + a 0 • L 0 + a 1 • L 0)
--       rw[add_assoc]
--       nth_rewrite 2 [← add_assoc]
--       rfl
--       rw[h6]
--       simp
--       rw[add_comm]



-- lemma equality_implies_subset (A B : Type) (f g : A → B): f = g → (∀ x, f x = g x)    := by
--   exact fun a x ↦ congrFun a x

-- #check vadd_left_mem_affineSpan_pair.mp
-- theorem volume_closed_segment (L : Segment) : (MeasureTheory.volume (closed_hull L)).toReal = 0 := by
--   apply Ennreal_zero_real_zero
--   apply MeasureTheory.measure_mono_null (segment_subset_affine_space L )
--   apply MeasureTheory.Measure.addHaar_affineSubspace
--   apply lt_top_iff_ne_top.mp
--   apply (AffineSubspace.lt_iff_le_and_exists (affineSpan ℝ {L 0, L 1}) ⊤).mpr
--   constructor
--   · exact fun ⦃a⦄ a ↦ trivial
--   · by_cases hL : L 0 ≠ L 1
--     · let a : ℝ² := (fun | 0 => - (L 1 - L 0) 1 | 1 => (L 1 - L 0) 0 )
--       have ha : a = (fun | 0 => - (L 1 - L 0) 1 | 1 => (L 1 - L 0) 0 ) := by rfl
--       use  a +ᵥ L 0
--       constructor
--       · trivial
--       · intro h
--         apply vadd_left_mem_affineSpan_pair.mp at h
--         cases' h with r h
--         rw[ha] at h
--         dsimp at h
--         apply fun a x ↦ congrFun a x at h
--         have h1 := h 0
--         have h2 := h 1
--         simp at *

--     · sorry
--         --rw[ha]


--     --use vadd_left_mem_affineSpan_pair



--We additionally want its flipped version

-- def flip_unit_triangle : Triangle  := fun | 0 => (v 1 1) | 1 => (v 0 1) | 2 => (v 1 0)
-- def open_flip_unit_triangle := open_hull flip_unit_triangle
-- def closed_flip_unit_triangle := closed_hull flip_unit_triangle

-- --Then additionally we have the diagonal
-- def diagonal_line : Segment := fun | 0 => (v 1 0) | 1 => (v 0 1)
-- def open_diagonal_line := open_hull diagonal_line

-- --We now want to show the open_unit_square is the disjoint union of these open triangles
-- --and the open diagonal


-- def union_of_open_triangles := open_unit_triangle  ∪ open_flip_unit_triangle




-- theorem open_unit_square1_is_union : open_unit_square1 = union_of_open_triangles ∪  open_diagonal_line := by
--   have hunit : unit_triangle = fun | 0 => (v 0 0) | 1 => (v 1 0) | 2 => (v 0 1) := by rfl
--   have hdiag : diagonal_line = fun | 0 => (v 1 0) | 1 => (v 0 1) := by rfl
--   have hflipunit: flip_unit_triangle = fun | 0 => (v 1 1) | 1 => (v 0 1) | 2 => (v 1 0) := by rfl
--   ext x
--   constructor
--   · rintro ⟨ h,h1,h2, h3 ⟩
--     have h7 := lt_trichotomy (x 0 +x 1) 1
--     rcases h7 with (h4 | h5| h6)
--     · left
--       left
--       use (fun | 0 => (1- x 0 - x 1) | 1 => x 0 | 2 => x 1)
--       constructor
--       · constructor
--         · dsimp
--           intro i
--           fin_cases i <;> dsimp <;> linarith
--         · rw[Fin.sum_univ_three]
--           dsimp
--           linarith
--       · dsimp
--         rw[Fin.sum_univ_three, hunit]
--         simp
--         ext i
--         fin_cases i <;> simp
--     · right
--       use (fun | 0 => x 0 | 1 => x 1 )
--       constructor
--       · constructor
--         · dsimp
--           intro i
--           fin_cases i <;> dsimp <;> linarith
--         · rw[Fin.sum_univ_two]
--           dsimp
--           linarith
--       · dsimp
--         rw[Fin.sum_univ_two,hdiag]
--         simp
--         ext i
--         fin_cases i <;> simp
--     · left
--       right
--       use (fun | 0 => (x 0 + x 1 -1) | 1 => 1 - x 0 | 2 => 1- x 1)
--       constructor
--       · constructor
--         · dsimp
--           intro i
--           fin_cases i <;> dsimp <;> linarith
--         · rw[Fin.sum_univ_three]
--           dsimp
--           linarith
--       · dsimp
--         rw[Fin.sum_univ_three, hflipunit]
--         simp
--         ext i
--         fin_cases i <;> simp
--   · intro h
--     cases' h  with h1 h2
--     cases' h1 with h1 h3
--     · rcases h1 with ⟨ a , ⟨ h4 ,h5⟩ ,h6⟩
--       rw[← h6]
--       dsimp
--       rw[Fin.sum_univ_three,hunit] at *
--       dsimp
--       refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> linarith[ h4 0 ,h4 1 ,h4 2, h4 3]
--     · rcases h3 with ⟨ a , ⟨ h4 ,h5⟩ ,h6⟩
--       rw[← h6]
--       dsimp
--       rw[Fin.sum_univ_three,hflipunit] at *
--       dsimp
--       refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> linarith[ h4 0 ,h4 1 ,h4 2, h4 3]
--     · rcases h2 with ⟨ a , ⟨ h4 ,h5⟩ ,h6⟩
--       rw[← h6]
--       dsimp
--       rw[Fin.sum_univ_two,hdiag] at *
--       dsimp
--       refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> linarith[ h4 0 ,h4 1 ,h4 2, h4 3]




-- theorem open_unit_squares_are_same : open_unit_square = open_unit_square1 := by
--   ext x
--   constructor
--   · rintro ⟨ a,⟨ ⟨ h2,h3⟩ ,h1⟩ ⟩
--     have hp : Psquare = (fun | 0 => v 0 0 | 1 => v 1 0 | 2 => v 1 1 | 3 => v 0 1) := by rfl
--     rw[← h1]
--     dsimp
--     rw[Fin.sum_univ_four,hp] at *
--     dsimp
--     refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> linarith[ h2 0 ,h2 1 ,h2 2, h2 3]
--   · sorry



-- theorem open_square_union_of : open_unit_square = union_of_open_triangles ∪  open_diagonal_line := by
--   rw[ open_unit_squares_are_same]
--   exact open_unit_square1_is_union
