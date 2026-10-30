module

public import SerrePositivity.HomologicalAlgebra.Complex.ConeLES
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone

/-! # 錐の連結射と一段シフトした錐の射影の符号

標準三角形の第3射は負の第1成分から作られる。
Milnor列の連結射と、元をそのまま保つ射影の対応を確認する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
variable (R : Type u) [CommRing R]
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ} (φ : K ⟶ L)

/-- 錐の連結射は、具体的な複体の第3射に対するshiftMap。 -/
theorem coneBoundary_eq_shiftMap (i j : ℤ) (h : i + 1 = j) :
    Cone.δ φ i j h =
      (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) 0).shiftMap
        (CochainComplex.mappingCone.triangle φ).mor₃ i j (by omega) := by
  rw [Cone.δ, CategoryTheory.Functor.homologySequenceδ]
  change (Cone.e i _).inv ≫
    (HomotopyCategory.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) 0).shiftMap
      (ShiftedHom.map (CochainComplex.mappingCone.triangle φ).mor₃
        (HomotopyCategory.quotient _ _)) i j _ ≫ (Cone.e j _).hom = _
  rw [HomotopyCategory.homologyFunctor_shiftMap]
  simp only [Iso.app_inv, Functor.comp_obj, Iso.app_hom, assoc,
    Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc]
  exact Category.comp_id _

/-- 三角形の第3射を一段戻すと、第1射影の負になる。 -/
theorem coneTriangle_shift_mor3 :
    (CochainComplex.mappingCone.triangle φ).mor₃⟦(-1 : ℤ)⟧' ≫
      (shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by omega)).hom.app K =
        -CochainComplex.mappingCocone.fst φ := by
  apply HomologicalComplex.hom_ext
  intro n
  simp [CochainComplex.mappingCocone.fst, CochainComplex.mappingCone.triangle,
    CochainComplex.HomComplex.Cochain.leftShift,
    CochainComplex.HomComplex.Cochain.rightShift,
    shiftFunctorCompIsoId, CochainComplex.shiftFunctorAdd'_inv_app_f',
    CochainComplex.shiftFunctorZero_hom_app_f, CochainComplex.shiftFunctorObjXIso,
    CochainComplex.HomComplex.Cochain.v_comp_XIsoOfEq_hom]

/-- 一段シフトの同定を経た連結射は、標準射影のホモロジー写像の負。 -/
theorem coneShiftBoundary_eq_neg_fst (i : ℤ) :
    ((CochainComplex.ShiftSequence.shiftIso (ModuleCat R) (-1) i (i - 1)
      (by omega)).app (CochainComplex.mappingCone φ)).hom ≫
      Cone.δ φ (i - 1) i (by omega) =
        -HomologicalComplex.homologyMap (CochainComplex.mappingCocone.fst φ) i := by
  rw [coneBoundary_eq_shiftMap]
  change ((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) 0).shiftIso
    (-1) i (i - 1) (by omega)).hom.app _ ≫ _ = _
  rw [CategoryTheory.Functor.shiftIso_hom_app_comp_shiftMap_of_add_eq_zero
    _ _ (-1) (by norm_num)]
  change HomologicalComplex.homologyMap
    ((CochainComplex.mappingCone.triangle φ).mor₃⟦(-1 : ℤ)⟧' ≫
      (shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by omega)).hom.app K) i = _
  rw [coneTriangle_shift_mor3]
  exact HomologicalComplex.homologyMap_neg _ _

end SerrePositivity.DerivedCompletion
