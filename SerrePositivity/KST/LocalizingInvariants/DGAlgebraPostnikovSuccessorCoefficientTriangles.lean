module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraShiftedLayerCochainNaturality
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorCoefficientLayerIsos

/-!
概要：次段切断候補の同じ係数 Γ の両三角形を、元の代数の H⁻⁽ⁿ⁺¹⁾ に移す。
方針：既存の厳密 cochain 三角形と、元の shift 層同型の自然性を合成する。
規約：class データで選んだ係数を保持。使われ方：実候補と元の f の πₙ₊₁ 三角形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} {hn : 0 ≤ n} {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovSuccessorClassInverseData R hn f j)

/-- Γ の作用を元の H⁻⁽ⁿ⁺¹⁾ の間の射として表す。 -/
def coefficientHomologyAction : (B.obj d.layerInverse.zero.stage).obj.X.homology (-(n + 1)) ⟶
    (A.obj j).obj.X.homology (-(n + 1)) :=
  (d.sourceCoefficientHomologyIso R).inv ≫ homologyMap (d.classCoefficient R).hom (-(n + 1) - 1) ≫
    (d.targetCoefficientHomologyIso R).hom

lemma classCoefficient_homology_right :
    homologyMap (d.classCoefficient R).hom (-(n + 1) - 1) ≫ (d.targetCoefficientHomologyIso R).hom ≫
      homologyMap (f.app j).hom.hom (-(n + 1)) =
    (d.sourceCoefficientHomologyIso R).hom ≫ homologyMap
      (B.transition (d.target_le.trans
        (d.layerInverse.zero.inverse_le.trans d.layerInverse.zero.stage_le))).hom.hom (-(n + 1)) := by
  let h := d.target_le.trans (d.layerInverse.zero.inverse_le.trans d.layerInverse.zero.stage_le)
  have hf := postnikovShiftedLayerHomologyIso_cochain_naturality R (f.app j).hom n hn 1
  have ht := postnikovShiftedLayerHomologyIso_cochain_naturality R
    (B.transition h).hom n hn 1
  change homologyMap ((postnikovLayerMap R (f.app j).hom n)⟦(1 : ℤ)⟧') (-(n + 1) - 1) ≫ _ =
    (d.targetCoefficientHomologyIso R).hom ≫ homologyMap (f.app j).hom.hom (-(n + 1)) at hf
  change homologyMap ((postnikovLayerMap R (B.transition h).hom n)⟦(1 : ℤ)⟧') (-(n + 1) - 1) ≫ _ =
    (d.sourceCoefficientHomologyIso R).hom ≫ homologyMap (B.transition h).hom.hom (-(n + 1)) at ht
  rw [← hf, ← Category.assoc, ← homologyMap_comp]
  change homologyMap ((d.classCoefficient R).hom ≫
    (postnikovLayerMap R (f.app j).hom n)⟦(1 : ℤ)⟧') (-(n + 1) - 1) ≫ _ = _
  rw [classCoefficient, PostnikovCommonCore.postnikovCommonClassCompatibilityCoefficient_right]
  exact ht

lemma coefficientHomologyAction_right : d.coefficientHomologyAction R ≫
    homologyMap (f.app j).hom.hom (-(n + 1)) = homologyMap
      (B.transition (d.target_le.trans
        (d.layerInverse.zero.inverse_le.trans d.layerInverse.zero.stage_le))).hom.hom (-(n + 1)) := by
  rw [coefficientHomologyAction, Category.assoc, Category.assoc,
    d.classCoefficient_homology_right R, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

lemma classCoefficient_homology_left :
    homologyMap ((postnikovLayerMap R (f.app d.layerInverse.zero.stage).hom n)⟦(1 : ℤ)⟧') (-(n + 1) - 1) ≫
      homologyMap (d.classCoefficient R).hom (-(n + 1) - 1) ≫ (d.targetCoefficientHomologyIso R).hom =
    (postnikovShiftedLayerHomologyIso R
      (A.obj d.layerInverse.zero.stage).obj n hn 1).hom ≫ homologyMap
      (A.transition (d.target_le.trans
        (d.layerInverse.zero.inverse_le.trans d.layerInverse.zero.stage_le))).hom.hom (-(n + 1)) := by
  rw [← Category.assoc, ← homologyMap_comp, classCoefficient,
    PostnikovCommonCore.postnikovCommonClassCompatibilityCoefficient_left]
  have ht := postnikovShiftedLayerHomologyIso_cochain_naturality R
    (A.transition (d.target_le.trans
      (d.layerInverse.zero.inverse_le.trans d.layerInverse.zero.stage_le))).hom n hn 1
  simpa only [Int.reduceAdd, Int.reduceNeg, Int.reduceSub,
    targetCoefficientHomologyIso, id_eq] using ht

lemma coefficientHomologyAction_left : homologyMap (f.app d.layerInverse.zero.stage).hom.hom (-(n + 1)) ≫
    d.coefficientHomologyAction R = homologyMap
      (A.transition (d.target_le.trans
        (d.layerInverse.zero.inverse_le.trans d.layerInverse.zero.stage_le))).hom.hom (-(n + 1)) := by
  let e := postnikovShiftedLayerHomologyIso R
    (A.obj d.layerInverse.zero.stage).obj n hn 1
  have hf := postnikovShiftedLayerHomologyIso_cochain_naturality R
    (f.app d.layerInverse.zero.stage).hom n hn 1
  apply (cancel_epi e.hom).1
  rw [← Category.assoc, ← hf]
  simp only [coefficientHomologyAction, sourceCoefficientHomologyIso, id_eq,
    Category.assoc, Iso.hom_inv_id_assoc]
  exact d.classCoefficient_homology_left R

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
