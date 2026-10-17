module
public import SerrePositivity.DifferentialGraded.Morita.CoherenceIdentityAugmentation
public import SerrePositivity.DifferentialGraded.Tensor.Triangle

/-! # 通常kernel作用の単位coherence

## 概要
通常のkernel合成比較と対角kernelの恒等比較が、既存bimodule単位子と整合する。

## 方針
bimodule射を入力加群で評価して作用の射へ比較し、既存三角図式を同じ評価で運ぶ。

## 規約と注意
局所Hom K-flat性は不要。全右加群型のSmallを仮定しない。

## 使われ方
U16aの公開導来作用の単位coherenceの計算モデル。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor BimoduleTensor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

/-- 入力族のbimodule射をtensorして評価すると、通常kernel作用の入力射になる。 -/
lemma kernelTensorFamilyMap (P : Bimodule A E D)
    (C : Type z) [DGCategory A C] {S T : BimoduleCategory A D C}
    (f : S ⟶ T) (c : C) :
    (BimoduleCategory.evaluation A E C c).map
      (composeMap A E D C (𝟙 (BimoduleCategory.of A E D P)) f) =
    (kernelTensor A D E P).onClosed.map ((BimoduleCategory.evaluation A D C c).map f) := by
  apply moduleMorphism_ext
  intro e
  change (BimoduleCategory.valueEvaluation A E C e c).map
      (composeMap A E D C (𝟙 (BimoduleCategory.of A E D P)) f) = _
  rw [composeMap_value_eval, kernelTensor_map_eval]
  unfold composeValueMap BalancedTensor.rightTensorMap BalancedTensor.rightTensorFunctor
  simp only [CategoryTheory.Functor.map_id]
  rfl

/-- 恒等kernelを先に作用させる比較は、通常bimodule右単位子と整合する。 -/
lemma kernelTensorCompositionClosedIso_rightUnit (P : Bimodule A E D)
    (M : ModuleCategory A D) :
    (kernelTensorCompositionClosedIso A D D E (Bimodule.diagonal A D) P).hom.app M ≫
      (kernelTensorMap A D E (rightBimoduleUnitIso A E D P).hom).app M =
    (kernelTensor A D E P).onClosed.map ((kernelIdentityClosedIso A D).hom.app M) := by
  let V := BimoduleCategory.evaluation A E (RightModule A D)
    (ForgetEnrichment.to (Complex A) M)
  let α := associatorIso A E D D (RightModule A D) P (Bimodule.diagonal A D)
    (DGFunctor.id (RightModule A D))
  have ht := triangle A E D (RightModule A D) P (DGFunctor.id (RightModule A D))
  have hi : α.inv ≫ composeMap A E D (RightModule A D) (rightBimoduleUnitIso A E D P).hom
      (𝟙 (BimoduleCategory.of A D (RightModule A D) (DGFunctor.id (RightModule A D)))) =
      composeMap A E D (RightModule A D) (𝟙 (BimoduleCategory.of A E D P))
        (leftBimoduleUnitIso A D (RightModule A D) (DGFunctor.id (RightModule A D))).hom := by
    rw [ht]
    exact α.inv_hom_id_assoc _
  have hv := congrArg V.map hi
  simp only [Functor.map_comp] at hv
  rw [kernelTensorCompositionClosedIso_hom_app]
  change V.map α.inv ≫ V.map
    (composeMap A E D (RightModule A D) (rightBimoduleUnitIso A E D P).hom
      (𝟙 (BimoduleCategory.of A D (RightModule A D) (DGFunctor.id (RightModule A D))))) = _
  rw [hv, kernelTensorFamilyMap]
  rfl

end SerrePositivity.DifferentialGraded.Morita
