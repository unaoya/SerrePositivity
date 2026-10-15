module
public import SerrePositivity.HomologicalAlgebra.CochainTensor
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.RingTheory.Flat.CategoryTheory

/-! # Tensoring with a complex in degree zero

This comparison identifies totalization with the ordinary pointwise tensor
functor, and will connect tensor products of resolutions to the existing Tor API.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex
variable {R : Type u} [CommRing R]

/-- The complex concentrated in degree zero with value V. -/
abbrev cochainSingleZero (V : ModuleCat.{u} R) : CochainComplex (ModuleCat.{u} R) ℤ :=
  (HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).obj V

variable (V : ModuleCat.{u} R) (P : CochainComplex (ModuleCat.{u} R) ℤ)

/-- Collapse the homogeneous coproduct when the left factor is concentrated in degree zero. -/
def tensorSingleLeftDesc (n : ℤ) :
    (cochainTensor (cochainSingleZero V) P).X n ⟶ V ⊗ P.X n :=
  HomologicalComplex₂.totalDesc _ (fun i j h => by
    by_cases hi : i = 0
    · subst i
      have hj : j = n := by dsimp at h; omega
      subst j
      exact (singleObjXSelf (.up ℤ) 0 V).hom ▷ P.X n
    · exact 0)

@[reassoc (attr := simp)]
lemma ι_tensorSingleLeftDesc (n : ℤ) :
    ιTensorObj (cochainSingleZero V) P 0 n n (zero_add n) ≫ tensorSingleLeftDesc V P n =
      (singleObjXSelf (.up ℤ) 0 V).hom ▷ P.X n := by
  simp [tensorSingleLeftDesc]

/-- Degreewise comparison with the ordinary pointwise tensor. -/
def tensorSingleLeftXIso (n : ℤ) :
    (cochainTensor (cochainSingleZero V) P).X n ≅ V ⊗ P.X n where
  hom := tensorSingleLeftDesc V P n
  inv := (singleObjXSelf (.up ℤ) 0 V).inv ▷ P.X n ≫
    ιTensorObj (cochainSingleZero V) P 0 n n (zero_add n)
  hom_inv_id := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro i j h
    by_cases hi : i = 0
    · subst i
      have hj : j = n := by dsimp at h; omega
      subst j
      simp [← comp_whiskerRight_assoc, -comp_whiskerRight]
    · have hz : IsZero ((cochainSingleZero V).X i) := isZero_single_obj_X _ _ _ i hi
      exact ((tensorRight (P.X j)).map_isZero hz).eq_of_src _ _
  inv_hom_id := by
    simp [-comp_whiskerRight]

/-- The inverse comparison intertwines the pointwise and total tensor differentials. -/
@[reassoc]
lemma tensorSingleLeftXIso_inv_d (n m : ℤ) (h : (ComplexShape.up ℤ).Rel n m) :
    (tensorSingleLeftXIso V P n).inv ≫ (cochainTensor (cochainSingleZero V) P).d n m =
      (V ◁ P.d n m) ≫ (tensorSingleLeftXIso V P m).inv := by
  dsimp at h
  subst m
  dsimp only [tensorSingleLeftXIso]
  rw [Category.assoc, ιTensorObj_cochainTensor_d]
  simp only [single_obj_d, MonoidalPreadditive.zero_whiskerRight, zero_comp, zero_add,
    Int.negOnePow_zero, one_smul, ← whisker_exchange_assoc]

/-- The total tensor with a degree-zero complex is naturally the ordinary tensor functor. -/
def cochainTensorSingleLeftIso :
    cochainTensor (cochainSingleZero V) P ≅ ((tensorLeft V).mapHomologicalComplex (.up ℤ)).obj P :=
  (HomologicalComplex.Hom.isoOfComponents (fun n => (tensorSingleLeftXIso V P n).symm)
    (fun n m h => tensorSingleLeftXIso_inv_d V P n m h)).symm

/-- Tensoring an acyclic complex with a flat module preserves acyclicity. -/
lemma cochainTensorSingleLeft_acyclic [Module.Flat R V] (hP : P.Acyclic) :
    (cochainTensor (cochainSingleZero V) P).Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have hz : IsZero ((((tensorLeft V).mapHomologicalComplex (.up ℤ)).obj P).homology i) := by
    exact ((P.sc i).mapHomologyIso (tensorLeft V)).isZero_iff.mpr
      ((tensorLeft V).map_isZero ((HomologicalComplex.exactAt_iff_isZero_homology P i).mp (hP i)))
  exact ((HomologicalComplex.homologyFunctor _ _ i).mapIso
    (cochainTensorSingleLeftIso V P)).isZero_iff.mpr hz
end SerrePositivity
