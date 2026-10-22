module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoCandidateRoof
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraQuasiIsoInverseRoofNaturality

/-!
概要：実二切断候補の class 模型での評価が、元の共通底への右脚を保つことを示す。
方針：四つの実模型射の右脚の式と、準同型逆 roof の脚の自然性を使う。
規約：ここは全準同型反転関手の界面。具体的不変量への移送は別工程。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)
  {D : Type v} [Category.{w} D] (L : Mon (Complex R) ⥤ D) (hL : InvertsQuasiIsos R L)

lemma classModelCandidateRoof_value_right :
    SurjectiveRoof.value R L hL (d.classModelCandidateRoof R) ≫
      L.map (HomotopyPullbackModel.right R
        (postnikovPerturbedClass R (A.obj j).obj 1 (by omega)) _) =
    L.map (HomotopyPullbackModel.right R (d.sourceClass R) _) ≫ L.map (d.targetBase R) := by
  let p₀ : d.sourceModel R ⟶ d.classBase R := HomotopyPullbackModel.right R _ _
  let p₂ : d.pathModel R ⟶ d.classBase R := HomotopyPullbackModel.right R _ _
  let p₃ : d.targetComposedModel R ⟶ d.classBase R := HomotopyPullbackModel.right R _ _
  let r : originalTargetModel (A := A) (j := j) R ⟶ postnikov R (A.obj j).obj 1 :=
    HomotopyPullbackModel.right R _ _
  have hT : (d.targetToStandard R ≫ d.targetToOriginalModel R) ≫ r = p₃ ≫ d.targetBase R := by
    rw [Category.assoc, d.targetToOriginalModel_right, ← Category.assoc, d.targetToStandard_right]
    rfl
  have hI : (d.sourceToImage R ≫ d.imageToPath R) ≫ p₂ = p₀ := by
    rw [Category.assoc, d.imageToPath_right, d.sourceToImage_right]
  have hN := SurjectiveRoof.inverse_value_naturality R (d.targetToPath R) L
    (d.targetToPath_quasiIso R) p₃ p₂ (d.targetToPath_right R) hL
  rw [classModelCandidateRoof, SurjectiveRoof.postcompose_value, SurjectiveRoof.comp_value,
    SurjectiveRoof.ofHom_value, Category.assoc, Category.assoc, ← L.map_comp, hT,
    L.map_comp p₃ (d.targetBase R), ← Category.assoc _ (L.map p₃), hN,
    ← Category.assoc, ← L.map_comp, hI]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
