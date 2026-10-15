module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FiniteTensorCoproduct
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FiniteTensorPushout
public import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty

/-! # Finite skeletal tensor attachments for an arbitrary left lifting class

This version has no model-category assumption on the ambient category.
It can in particular be applied in an arrow category without first
constructing a model structure on that arrow category.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.HomotopyFunctionComplex.FiniteTensor.LiftingClass
open SSet.relativeCellComplexOfMono
variable {C : Type u} [Category.{v} C] [HasFiniteColimits C] (A : SimplexCategory ⥤ C)
  (Q : MorphismProperty C)
  (hboundary : ∀ n : ℕ, Q.llp (map A (SSet.boundary.{v} n).ι))
  {X Y : SSet.{v}} [X.Nonsingular] [X.Finite] [Y.Nonsingular] [Y.Finite]
  (i : X ⟶ Y) [Mono i]

instance cell_finite (d : ℕ) : Finite (Cell i d) :=
  Finite.of_injective (fun c : Cell i d ↦ (⟨c.simplex, c.nonDegenerate⟩ : Y.nonDegenerate d))
    (fun _ _ h ↦ Cell.ext (congrArg Subtype.val h))

include hboundary in
omit [X.Nonsingular] [X.Finite] [Y.Nonsingular] [Mono i] in
lemma skeleton_l_mem (d : ℕ) : Q.llp (map A (l i d)) :=
  map_sigma_mem A (fun _ : Cell i d ↦ (SSet.boundary.{v} d).toSSet)
    (fun _ ↦ SSet.stdSimplex.obj (SimplexCategory.mk d))
    (fun _ ↦ (SSet.boundary.{v} d).ι) Q.llp
    (fun _ ↦ hboundary d)

include hboundary in
omit [X.Nonsingular] [X.Finite] [Mono i] in
lemma skeleton_r_mem (d : ℕ) : Q.llp (map A (r i d)) :=
  Q.llp.of_isPushout
    (FiniteTensor.isPushout A (SSet.relativeCellComplexOfMono.isPushout i d))
    (skeleton_l_mem A Q hboundary i d)

include hboundary in
omit [X.Nonsingular] [X.Finite] [Mono i] in
lemma skeleton_zero_mem (d : ℕ) :
    Q.llp (map A (SSet.Subcomplex.homOfLE
      ((SSet.skeletonOfMono i).monotone (Nat.zero_le d)))) := by
  induction d with
  | zero =>
    simpa only [SSet.Subcomplex.homOfLE_refl, map_id] using
      Q.llp.id_mem (obj A (SSet.skeletonOfMono i 0).toSSet)
  | succ d hd =>
    exact (map_comp A (SSet.Subcomplex.homOfLE
      ((SSet.skeletonOfMono i).monotone (Nat.zero_le d))) (r i d)) ▸
      Q.llp.comp_mem _ _ hd (skeleton_r_mem A Q hboundary i d)

include hboundary in
/-- Boundary lifting properties extend to every finite nonsingular monomorphism.
The ambient category needs only finite colimits, with no model structure. -/
lemma map_mono_mem : Q.llp (map A i) := by
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
  have h := Q.llp.comp_mem _ _ (Q.llp_of_isIso (map A e₀.hom))
    (Q.llp.comp_mem _ _ (skeleton_zero_mem A Q hboundary i d)
      (Q.llp_of_isIso (map A e₁.hom)))
  have hm : map A e₀.hom ≫ (map A j ≫ map A e₁.hom) = map A i :=
    (congrArg (fun f ↦ map A e₀.hom ≫ f) (map_comp A j e₁.hom)).trans
      ((map_comp A e₀.hom (j ≫ e₁.hom)).trans (congrArg (map A) he))
  exact hm ▸ h


end SerrePositivity.HomotopyFunctionComplex.FiniteTensor.LiftingClass
