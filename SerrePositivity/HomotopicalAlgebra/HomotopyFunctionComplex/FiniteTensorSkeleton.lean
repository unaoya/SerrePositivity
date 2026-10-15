module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FiniteTensorCoproduct
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FiniteTensorBoundary
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FiniteTensorPushout
public import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton

/-! # Finite skeletal attachments under a Reedy cofibrant tensor

The cell family of a finite target is finite in every dimension. The
actual Mathlib skeletal pushout therefore maps to a pushout in C whose
attaching map is a coproduct of constructed boundary cofibrations.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.HomotopyFunctionComplex.FiniteTensor
open SSet.relativeCellComplexOfMono
variable {C : Type u} [Category.{v} C] [ModelCategory C] (A : SimplexCategory ⥤ C)
  (hA : reedyLeft simplex (cofibrations C) (initial.to A))
  {X Y : SSet.{v}} [X.Nonsingular] [X.Finite] [Y.Nonsingular] [Y.Finite]
  (i : X ⟶ Y) [Mono i]

instance cell_finite (d : ℕ) : Finite (Cell i d) :=
  Finite.of_injective (fun c : Cell i d ↦ (⟨c.simplex, c.nonDegenerate⟩ : Y.nonDegenerate d))
    (fun _ _ h ↦ Cell.ext (congrArg Subtype.val h))

include hA in
omit [X.Nonsingular] [X.Finite] [Y.Nonsingular] [Mono i] in
lemma skeleton_l_cofibration (d : ℕ) : cofibrations C (map A (l i d)) :=
  map_sigma_mem A (fun _ : Cell i d ↦ (SSet.boundary.{v} d).toSSet)
    (fun _ ↦ SSet.stdSimplex.obj (SimplexCategory.mk d))
    (fun _ ↦ (SSet.boundary.{v} d).ι) (cofibrations C)
    (fun _ ↦ finiteTensor_boundary_cofibration A hA d)

include hA in
omit [X.Nonsingular] [X.Finite] [Mono i] in
lemma skeleton_r_cofibration (d : ℕ) : cofibrations C (map A (r i d)) :=
  (cofibrations C).of_isPushout
    (FiniteTensor.isPushout A (SSet.relativeCellComplexOfMono.isPushout i d))
    (skeleton_l_cofibration A hA i d)

include hA in
omit [X.Nonsingular] [X.Finite] [Mono i] in
lemma skeleton_zero_cofibration (d : ℕ) :
    cofibrations C (map A (SSet.Subcomplex.homOfLE
      ((SSet.skeletonOfMono i).monotone (Nat.zero_le d)))) := by
  induction d with
  | zero =>
    simpa only [SSet.Subcomplex.homOfLE_refl, map_id] using
      (cofibrations C).id_mem (obj A (SSet.skeletonOfMono i 0).toSSet)
  | succ d hd =>
    exact (map_comp A (SSet.Subcomplex.homOfLE
      ((SSet.skeletonOfMono i).monotone (Nat.zero_le d))) (r i d)) ▸
      (cofibrations C).comp_mem _ _ hd (skeleton_r_cofibration A hA i d)

include hA in
/-- Finite nonsingular monomorphisms are sent to cofibrations. Only finite
colimits are used: the relative skeletal filtration terminates in finite degree. -/
lemma map_mono_cofibration : cofibrations C (map A i) := by
  obtain ⟨d, hd⟩ := Y.hasDimensionLT_of_finite
  let := hd
  have ht : SSet.skeletonOfMono i d = ⊤ := by
    rw [SSet.Subcomplex.eq_top_iff_contains_nonDegenerate]
    intro n x hx
    exact (SSet.mem_skeletonOfMono_obj_iff_of_nonDegenerate i ⟨x, hx⟩ d).mpr
      (Or.inr (Y.dim_lt_of_nonDegenerate ⟨x, hx⟩ d))
  let e₀ : X ≅ (SSet.skeletonOfMono i 0).toSSet :=
    asIso (SSet.Subcomplex.toRange i) ≪≫
      SSet.Subcomplex.eqToIso (SSet.skeletonOfMono_zero i).symm
  let e₁ : (SSet.skeletonOfMono i d).toSSet ≅ Y :=
    SSet.Subcomplex.eqToIso ht ≪≫ SSet.Subcomplex.topIso Y
  let j := SSet.Subcomplex.homOfLE ((SSet.skeletonOfMono i).monotone (Nat.zero_le d))
  have he : e₀.hom ≫ j ≫ e₁.hom = i := by
    ext n x
    rfl
  have : IsIso (map A e₀.hom) := inferInstanceAs (IsIso (iso A e₀).hom)
  have : IsIso (map A e₁.hom) := inferInstanceAs (IsIso (iso A e₁).hom)
  have h := (cofibrations C).comp_mem _ _ ((cofibrations C).of_isIso (map A e₀.hom))
    ((cofibrations C).comp_mem _ _ (skeleton_zero_cofibration A hA i d)
      ((cofibrations C).of_isIso (map A e₁.hom)))
  have hm : map A e₀.hom ≫ (map A j ≫ map A e₁.hom) = map A i :=
    (congrArg (fun f ↦ map A e₀.hom ≫ f) (map_comp A j e₁.hom)).trans
      ((map_comp A e₀.hom (j ≫ e₁.hom)).trans (congrArg (map A) he))
  exact hm ▸ h

end SerrePositivity.HomotopyFunctionComplex.FiniteTensor

namespace SerrePositivity.HomotopyFunctionComplex
variable {C : Type u} [Category.{v} C] [ModelCategory C] (A : SimplexCategory ⥤ C)

/-- Every subcomplex of a standard simplex gives a cofibration in the source
under a Reedy cofibrant tensor, including every horn. -/
lemma subcomplexTensor_cofibration
    (hA : reedyLeft simplex (cofibrations C) (initial.to A))
    {n : SimplexCategory} (S : (SSet.stdSimplex.{v}.obj n).Subcomplex) :
    cofibrations C (SubcomplexTensor.inclusion S A) :=
  ((cofibrations C).arrow_iso_iff (finiteTensorInclusionArrowIso A S)).mp
    (FiniteTensor.map_mono_cofibration A hA S.ι)

end SerrePositivity.HomotopyFunctionComplex
