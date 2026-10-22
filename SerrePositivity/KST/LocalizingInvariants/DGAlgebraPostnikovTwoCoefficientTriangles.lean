module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraShiftedLayerCochainNaturality
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoCoefficientLayerIsos

/-!
概要：二切断候補の同じ係数 Γ の両三角形を、元の代数の H⁻² に移す。
方針：既存の厳密 cochain 三角形と、元の shift 層同型の自然性を合成する。
規約：class データで選んだ係数を保持。使われ方：実候補と元の f の π₂ 三角形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

/-- Γ の作用を元の H⁻² の間の射として表す。 -/
def coefficientHomologyAction : (B.obj d.layerInverse.zero.stage).obj.X.homology (-2) ⟶
    (A.obj j).obj.X.homology (-2) :=
  (d.sourceCoefficientHomologyIso R).inv ≫ homologyMap (d.classCoefficient R).hom (-3) ≫
    (d.targetCoefficientHomologyIso R).hom

lemma classCoefficient_homology_right :
    homologyMap (d.classCoefficient R).hom (-3) ≫ (d.targetCoefficientHomologyIso R).hom ≫
      homologyMap (f.app j).hom.hom (-2) =
    (d.sourceCoefficientHomologyIso R).hom ≫ homologyMap
      (B.transition (d.target_le.trans
        (d.layerInverse.zero.inverse_le.trans d.layerInverse.zero.stage_le))).hom.hom (-2) := by
  let h := d.target_le.trans (d.layerInverse.zero.inverse_le.trans d.layerInverse.zero.stage_le)
  have hf := postnikovShiftedLayerHomologyIso_cochain_naturality R (f.app j).hom 1 (by omega) 1
  have ht := postnikovShiftedLayerHomologyIso_cochain_naturality R
    (B.transition h).hom 1 (by omega) 1
  simp only [Int.reduceAdd, Int.reduceNeg, Int.reduceSub] at hf ht
  change homologyMap ((postnikovLayerMap R (f.app j).hom 1)⟦(1 : ℤ)⟧') (-3) ≫ _ =
    (d.targetCoefficientHomologyIso R).hom ≫ homologyMap (f.app j).hom.hom (-2) at hf
  change homologyMap ((postnikovLayerMap R (B.transition h).hom 1)⟦(1 : ℤ)⟧') (-3) ≫ _ =
    (d.sourceCoefficientHomologyIso R).hom ≫ homologyMap (B.transition h).hom.hom (-2) at ht
  rw [← hf, ← Category.assoc, ← homologyMap_comp]
  change homologyMap ((d.classCoefficient R).hom ≫
    (postnikovLayerMap R (f.app j).hom 1)⟦(1 : ℤ)⟧') (-3) ≫ _ = _
  rw [classCoefficient, postnikovCommonClassCompatibilityCoefficient_right]
  exact ht

lemma coefficientHomologyAction_right : d.coefficientHomologyAction R ≫
    homologyMap (f.app j).hom.hom (-2) = homologyMap
      (B.transition (d.target_le.trans
        (d.layerInverse.zero.inverse_le.trans d.layerInverse.zero.stage_le))).hom.hom (-2) := by
  rw [coefficientHomologyAction, Category.assoc, Category.assoc,
    d.classCoefficient_homology_right R, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

lemma classCoefficient_homology_left :
    homologyMap ((postnikovLayerMap R (f.app d.layerInverse.zero.stage).hom 1)⟦(1 : ℤ)⟧') (-3) ≫
      homologyMap (d.classCoefficient R).hom (-3) ≫ (d.targetCoefficientHomologyIso R).hom =
    (postnikovShiftedLayerHomologyIso R
      (A.obj d.layerInverse.zero.stage).obj 1 (by omega) 1).hom ≫ homologyMap
      (A.transition (d.target_le.trans
        (d.layerInverse.zero.inverse_le.trans d.layerInverse.zero.stage_le))).hom.hom (-2) := by
  rw [← Category.assoc, ← homologyMap_comp, classCoefficient,
    postnikovCommonClassCompatibilityCoefficient_left]
  have ht := postnikovShiftedLayerHomologyIso_cochain_naturality R
    (A.transition (d.target_le.trans
      (d.layerInverse.zero.inverse_le.trans d.layerInverse.zero.stage_le))).hom 1 (by omega) 1
  simpa only [Int.reduceAdd, Int.reduceNeg, Int.reduceSub,
    targetCoefficientHomologyIso, id_eq] using ht

lemma coefficientHomologyAction_left : homologyMap (f.app d.layerInverse.zero.stage).hom.hom (-2) ≫
    d.coefficientHomologyAction R = homologyMap
      (A.transition (d.target_le.trans
        (d.layerInverse.zero.inverse_le.trans d.layerInverse.zero.stage_le))).hom.hom (-2) := by
  let e := postnikovShiftedLayerHomologyIso R
    (A.obj d.layerInverse.zero.stage).obj 1 (by omega) 1
  have hf := postnikovShiftedLayerHomologyIso_cochain_naturality R
    (f.app d.layerInverse.zero.stage).hom 1 (by omega) 1
  simp only [Int.reduceAdd, Int.reduceNeg, Int.reduceSub] at hf
  apply (cancel_epi e.hom).1
  rw [← Category.assoc, ← hf]
  simp only [coefficientHomologyAction, sourceCoefficientHomologyIso, id_eq,
    Category.assoc, Iso.hom_inv_id_assoc]
  exact d.classCoefficient_homology_left R

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
