module

public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceRoofFrame
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointPairingCorrection
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotProbeNativeHomComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedPairingZero

/-!
概要：同じ元の source-frame 単位ラベルと native pairing の零次の値。
方針：全 pairing の既存の同じラベルを読む法則を、元のBEの増大写像と単位へ適用する。
規約：同じモデル源と同じ単位を保持する。native 比較の弱同値性はまだ主張しない。
使われ方：元の corrected pairing の単位の評価への接続。
-/

@[expose] public section
open CategoryTheory HomotopicalAlgebra SSet
open scoped Simplicial
open SerrePositivity.EInfinity.BarrattEccles
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
noncomputable section

namespace SerrePositivity.EInfinity.BarrattEccles
variable (A : Type u) [CommRing A]
local instance jointSourceUnitLabelModel : ModelCategory (operad A).Algebra := modelCategory A
local instance jointSourceUnitLabelFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩

/-- 元の試験対象と同じ標的を持つ、元の共同添字。 -/
def strictBETotJointUnitIndex (X : (operad A).Algebra) : strictBETotJointHomIndex A :=
  AsSmall.up.obj (Opposite.op X, X)

/-- 元の次数0の増大写像・probe 比較・標的単位の同じ合成を全要素のラベルとして読む。 -/
def strictBETotJointSourceUnitLabel (X : (operad A).Algebra) : StrictBETotJointSourceElements A :=
  { obj := (strictBETotJointUnitIndex A X, Opposite.op ⦋0⦌)
    val := ULift.up (((strictBETotJointRoofResolution A (strictBETotJointUnitIndex A X)).augmentation.app ⦋0⦌ ≫
      framedLimitProbeComparison A X) ≫
      ((rightFrameUnit (rightFrameFamily A)).app X).app (Opposite.op ⦋0⦌)) }


/-- 元の全 pairing の零単体は、同じラベルの実射を同じモデル源へ送ったもの。 -/
lemma strictBETotJointSourceNativePairing_vertex (t : StrictBETotJointSourceElements A) :
    (strictBETotJointSourceNativePairing A).app (Opposite.op ⦋0⦌)
      (SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex t) =
      (edgewiseWeightIso 0).hom ≫ SSet.yonedaEquiv.symm
        (ComposableArrows.mk₁ (SerrePositivity.EInfinity.FrameHom.liftedSourceFrameArrowValue
          (strictBETotJointSourceFrame A) (rightFrameReplacement (rightFrameFamily A)) t)) ≫
            strictBETotModelSource A := by
  exact twistedPairingNerveMap_zero_postcomp _ _ _ (strictBETotModelSource A)
    (SerrePositivity.EInfinity.FrameHom.liftedSourceFrameArrowValue_naturality
      (strictBETotJointSourceFrame A) (rightFrameReplacement (rightFrameFamily A))) t

/-- 同じ単位ラベルの実射を読むと、元の三つの射の同じ合成へ戻る。 -/
lemma strictBETotJointSourceUnitLabel_value (X : (operad A).Algebra) :
    SerrePositivity.EInfinity.FrameHom.liftedSourceFrameArrowValue
      (strictBETotJointSourceFrame A) (rightFrameReplacement (rightFrameFamily A))
      (strictBETotJointSourceUnitLabel A X) =
      (AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).map
        (((strictBETotJointRoofResolution A (strictBETotJointUnitIndex A X)).augmentation.app ⦋0⦌ ≫
          framedLimitProbeComparison A X) ≫
          ((rightFrameUnit (rightFrameFamily A)).app X).app (Opposite.op ⦋0⦌)) := rfl

/-- 元の単位ラベルの native pairing の像を、元の三射の同じ合成として回収する。 -/
lemma strictBETotJointSourceUnitLabel_native_pairing (X : (operad A).Algebra) :
    (strictBETotJointSourceNativePairing A).app (Opposite.op ⦋0⦌)
      (SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex
        (strictBETotJointSourceUnitLabel A X)) =
      (edgewiseWeightIso 0).hom ≫ SSet.yonedaEquiv.symm
        (ComposableArrows.mk₁ ((AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).map
          (((strictBETotJointRoofResolution A (strictBETotJointUnitIndex A X)).augmentation.app ⦋0⦌ ≫
            framedLimitProbeComparison A X) ≫
            ((rightFrameUnit (rightFrameFamily A)).app X).app (Opposite.op ⦋0⦌)))) ≫
              strictBETotModelSource A := by
  rw [strictBETotJointSourceNativePairing_vertex, strictBETotJointSourceUnitLabel_value]
end SerrePositivity.EInfinity.BarrattEccles

end
