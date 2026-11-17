module

public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointSourceRoofFrame
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointPairingCorrection
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotProbeNativeHomComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedPairingZero

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：同じ元の source-frame 単位ラベルと native pairing の零次の値。
方針：全 pairing の既存の同じラベルを読む法則を、元のBEの増大写像と単位へ適用する。
規約：同じモデル源と同じ単位を保持する。native 比較の弱同値性はまだ主張しない。
使われ方：元の corrected pairing の単位の評価への接続。
-/

@[expose] public section
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.SSet
open scoped _root_.Simplicial
open _root_.SerrePositivity.EInfinity.BarrattEccles
open _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
noncomputable section

namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
variable (A : Type u) [CommRing A]
local instance jointSourceUnitLabelModel : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A
local instance jointSourceUnitLabelFactorization :
    (cofibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) := ⟨⟨_root_.SerrePositivity.EInfinity.BarrattEccles.mappingCofibrantFactorization A⟩⟩

/-- 元の試験対象と同じ標的を持つ、元の共同添字。 -/
def strictBETotJointUnitIndex (X : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A :=
  AsSmall.up.obj (Opposite.op X, X)

/-- 元の次数0の増大写像・probe 比較・標的単位の同じ合成を全要素のラベルとして読む。 -/
def strictBETotJointSourceUnitLabel (X : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictBETotJointSourceElements A :=
  { obj := (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointUnitIndex A X, Opposite.op ⦋0⦌)
    val := ULift.up (((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofResolution A (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointUnitIndex A X)).augmentation.app ⦋0⦌ ≫
      _root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeComparison A X) ≫
      ((rightFrameUnit (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A)).app X).app (Opposite.op ⦋0⦌)) }


/-- 元の全 pairing の零単体は、同じラベルの実射を同じモデル源へ送ったもの。 -/
lemma strictBETotJointSourceNativePairing_vertex (t : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictBETotJointSourceElements A) :
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativePairing A).app (Opposite.op ⦋0⦌)
      (SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex t) =
      (edgewiseWeightIso 0).hom ≫ SSet.yonedaEquiv.symm
        (ComposableArrows.mk₁ (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.liftedSourceFrameArrowValue
          (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrame A) (rightFrameReplacement (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A)) t)) ≫
            _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A := by
  exact twistedPairingNerveMap_zero_postcomp _ _ _ (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A)
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.liftedSourceFrameArrowValue_naturality
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrame A) (rightFrameReplacement (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A))) t

/-- 同じ単位ラベルの実射を読むと、元の三つの射の同じ合成へ戻る。 -/
lemma strictBETotJointSourceUnitLabel_value (X : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.liftedSourceFrameArrowValue
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrame A) (rightFrameReplacement (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A))
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceUnitLabel A X) =
      (AsSmall.up : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra ⥤ AsSmall.{u+1} (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).map
        (((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofResolution A (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointUnitIndex A X)).augmentation.app ⦋0⦌ ≫
          _root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeComparison A X) ≫
          ((rightFrameUnit (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A)).app X).app (Opposite.op ⦋0⦌)) := rfl

/-- 元の単位ラベルの native pairing の像を、元の三射の同じ合成として回収する。 -/
lemma strictBETotJointSourceUnitLabel_native_pairing (X : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativePairing A).app (Opposite.op ⦋0⦌)
      (SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex
        (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceUnitLabel A X)) =
      (edgewiseWeightIso 0).hom ≫ SSet.yonedaEquiv.symm
        (ComposableArrows.mk₁ ((AsSmall.up : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra ⥤ AsSmall.{u+1} (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).map
          (((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofResolution A (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointUnitIndex A X)).augmentation.app ⦋0⦌ ≫
            _root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeComparison A X) ≫
            ((rightFrameUnit (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A)).app X).app (Opposite.op ⦋0⦌)))) ≫
              _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A := by
  rw [_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativePairing_vertex, _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceUnitLabel_value]
end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot

end
