module
public import SerrePositivity.HomologicalAlgebra.CochainLinearDualCone
public import SerrePositivity.HomologicalAlgebra.KoszulTensorConeComparison
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-! # Self-duality of the iterated-cone Koszul complex -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {R : Type u} [CommRing R]

/-- Dualizing a scalar endomorphism gives the same scalar on the coefficient dual. -/
lemma cochainLinearDualMap_smul_id (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (M : ModuleCat.{u} R) :
    (cochainLinearDualMap (a • 𝟙 K)).app M = a • 𝟙 ((cochainLinearDualFunctor K).obj M) := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro g
  change (a • 𝟙 (K.X (0 - i))) ≫ g = a • g
  simp only [Linear.smul_comp, Category.id_comp]

/-- The dual of a scalar cone is the scalar cone of the dual, shifted by minus one. -/
def scalarConeLinearDualIso (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (M : ModuleCat.{u} R) :
    (cochainLinearDualFunctor ((scalarConeFunctor a).obj K)).obj M ≅
      ((scalarConeFunctor a).obj ((cochainLinearDualFunctor K).obj M))⟦(-1 : ℤ)⟧ := by
  have he : (cochainLinearDualMap (a • 𝟙 K)).app M =
      a • 𝟙 ((cochainLinearDualFunctor K).obj M) :=
    cochainLinearDualMap_smul_id a K M
  exact cochainLinearDualConeIso (a • 𝟙 K) M ≪≫
    (shiftFunctor _ (-1 : ℤ)).mapIso (eqToIso (by rw [he]; rfl))

/-- The integer dual of a degree-zero single complex has zero differential. -/
lemma cochainLinearDualSingle_d (N M : ModuleCat.{u} R) (i j : ℤ) :
    ((cochainLinearDualFunctor ((single (ModuleCat R) (.up ℤ) 0).obj N)).obj M).d i j = 0 := by
  apply ModuleCat.hom_ext
  ext f
  change ((single (ModuleCat R) (.up ℤ) 0).obj N).d (0 - j) (0 - i) ≫ f = 0
  rw [single_obj_d, zero_comp]

/-- Duality for a single complex is the usual module Hom, concentrated in degree zero. -/
def cochainLinearDualSingleTermIso (N M : ModuleCat.{u} R) (i : ℤ) :
    ((cochainLinearDualFunctor ((single (ModuleCat R) (.up ℤ) 0).obj N)).obj M).X i ≅
      ((single (ModuleCat R) (.up ℤ) 0).obj (ModuleCat.of R (N ⟶ M))).X i := by
  by_cases hi : i = 0
  · subst i
    exact (Linear.homCongr R (singleObjXSelf (.up ℤ) 0 N) (Iso.refl M)).toModuleIso ≪≫
      (singleObjXSelf (.up ℤ) 0 (ModuleCat.of R (N ⟶ M))).symm
  · have hz := isZero_single_obj_X (.up ℤ) 0 N (0 - i) (by omega)
    haveI : Subsingleton
        (((cochainLinearDualFunctor ((single (ModuleCat R) (.up ℤ) 0).obj N)).obj M).X i) :=
      ⟨fun f g => hz.eq_of_src f g⟩
    exact (ModuleCat.isZero_of_subsingleton _).iso
      (isZero_single_obj_X (.up ℤ) 0 (ModuleCat.of R (N ⟶ M)) i hi)

/-- Duality of single complexes as an actual complex isomorphism. -/
def cochainLinearDualSingleIso (N M : ModuleCat.{u} R) :
    (cochainLinearDualFunctor ((single (ModuleCat R) (.up ℤ) 0).obj N)).obj M ≅
      (single (ModuleCat R) (.up ℤ) 0).obj (ModuleCat.of R (N ⟶ M)) :=
  HomologicalComplex.Hom.isoOfComponents (cochainLinearDualSingleTermIso N M)
    (fun i j _ => by rw [single_obj_d, cochainLinearDualSingle_d, comp_zero, zero_comp])

/-- Evaluation at one identifies the dual of the empty Koszul complex with its coefficients. -/
def koszulLinearDualEmptyIso (z : Fin 0 → R) (M : ModuleCat.{u} R) :
    (cochainLinearDualFunctor (koszulComplex z)).obj M ≅ (koszulModuleFunctor z).obj M :=
  cochainLinearDualSingleIso (ModuleCat.of R R) M ≪≫
    (single (ModuleCat R) (.up ℤ) 0).mapIso
      (((ModuleCat.homLinearEquiv : ((ModuleCat.of R R) ⟶ M) ≃ₗ[R] (R →ₗ[R] M)).trans
        (LinearMap.ringLmapEquivSelf R R M)).toModuleIso)

/-- Scalar cones commute with shifts through the standard signed cone comparison. -/
def scalarConeShiftIso (a : R) (P : CochainComplex (ModuleCat.{u} R) ℤ) (m : ℤ) :
    ((scalarConeFunctor a).obj P)⟦m⟧ ≅ (scalarConeFunctor a).obj (P⟦m⟧) := by
  have he : (smulId a P)⟦m⟧' = smulId a (P⟦m⟧) := by
    simp [smulId, Functor.map_smul]
  exact CochainComplex.mappingCone.shiftIso (smulId a P) m ≪≫
    eqToIso (by rw [he]; rfl)

/-- The actual dual of a length-e Koszul complex is its coefficient complex shifted by minus e. -/
def koszulLinearDualIso : ∀ {e : ℕ} (z : Fin e → R) (M : ModuleCat.{u} R),
    (cochainLinearDualFunctor (koszulComplex z)).obj M ≅
      ((koszulModuleFunctor z).obj M)⟦(-(e : ℤ))⟧
  | 0, z, M => koszulLinearDualEmptyIso z M ≪≫
      ((shiftFunctorZero (CochainComplex (ModuleCat.{u} R) ℤ) ℤ).app
        ((koszulModuleFunctor z).obj M)).symm
  | n + 1, z, M =>
      let a := z (Fin.last n)
      let P := (koszulModuleFunctor (Fin.init z)).obj M
      scalarConeLinearDualIso a (koszulComplex (Fin.init z)) M ≪≫
        (shiftFunctor _ (-1 : ℤ)).mapIso
          ((scalarConeFunctor a).mapIso (koszulLinearDualIso (Fin.init z) M) ≪≫
            (scalarConeShiftIso a P (-(n : ℤ))).symm) ≪≫
        ((shiftFunctorAdd' (CochainComplex (ModuleCat.{u} R) ℤ)
          (-(n : ℤ)) (-1) (-((n + 1 : ℕ) : ℤ)) (by omega)).app
            ((scalarConeFunctor a).obj P)).symm

/-- Degree-i dual Koszul cohomology corresponds to degree i-e coefficient Koszul cohomology. -/
def koszulLinearDualHomologyIso {e : ℕ} (z : Fin e → R) (M : ModuleCat.{u} R) (i : ℤ) :
    ((cochainLinearDualFunctor (koszulComplex z)).obj M).homology i ≅
      ((koszulModuleFunctor z).obj M).homology (i - (e : ℤ)) :=
  (homologyFunctor (ModuleCat R) (.up ℤ) i).mapIso (koszulLinearDualIso z M) ≪≫
    (CochainComplex.ShiftSequence.shiftIso (ModuleCat R) (-(e : ℤ)) i
      (i - (e : ℤ)) (by omega)).app ((koszulModuleFunctor z).obj M)

end SerrePositivity
