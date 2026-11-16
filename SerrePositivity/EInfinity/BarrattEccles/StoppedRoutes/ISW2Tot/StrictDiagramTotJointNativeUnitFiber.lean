module

public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointCorrectedUnitArrow
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointSourceNativeFiberPairing

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：同じnative fiber射の元の単位点の辺の類を回収する。
方針：元のfiber包含の厳密な等式を同じ単位の頂点で評価する。
規約：元の係数・単位ラベル・pullback同型・補正済pairingを保持する。
使われ方：全native比較の元の単位の評価の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.SSet
open scoped _root_.Simplicial
open _root_.SerrePositivity.EInfinity.BarrattEccles
open _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

noncomputable section

namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot

variable (A : Type u) [CommRing A]
local instance jointNativeUnitFiberModel : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A
local instance jointNativeUnitFiberFactorization :
    (cofibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) := ⟨⟨_root_.SerrePositivity.EInfinity.BarrattEccles.mappingCofibrantFactorization A⟩⟩

/-- 元の単位ラベルを、同じ係数の全要素の同じfiber内の対象として取る。 -/
def strictBETotJointSourceNativeUnitFiberElement (X : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    (simplicialElementsCatDiagram (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A)).obj
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointUnitIndex A X) :=
  { obj := Opposite.op ⦋0⦌
    val := (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceUnitLabel A X).val }

/-- 同じfiberの対象を元の全要素へ戻すと、元の単位ラベルそのもの。 -/
lemma strictBETotJointSourceNativeUnitFiberElement_value (X : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    (simplicialElementsFiberFunctor (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A)
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointUnitIndex A X)).obj (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativeUnitFiberElement A X) =
        _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceUnitLabel A X := rfl

/-- 同じnative fiber射の単位の値は、元の補正済pairingの同じ単位の値。 -/
lemma strictBETotJointSourceNativeTwistedFiberMap_unit_value (X : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativeTwistedFiberMap A (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointUnitIndex A X)).app
      (Opposite.op ⦋0⦌) (nerveVertex (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativeUnitFiberElement A X))).val =
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectedPairing A).app (Opposite.op ⦋0⦌)
        (nerveVertex (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceUnitLabel A X)) := by
  have h := congrArg (fun f => f.app (Opposite.op ⦋0⦌)
      (nerveVertex (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativeUnitFiberElement A X)))
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativeTwistedFiberMap_ι A (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointUnitIndex A X))
  rw [simplicialElementsFiberInclusion_eq_nerveMap] at h
  have hv : (nerveMap (simplicialElementsFiberFunctor (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A)
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointUnitIndex A X))).app (Opposite.op ⦋0⦌)
      (nerveVertex (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativeUnitFiberElement A X)) =
        nerveVertex (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceUnitLabel A X) :=
    ComposableArrows.ext₀ rfl
  change ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativeTwistedFiberMap A (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointUnitIndex A X)).app
    (Opposite.op ⦋0⦌) (nerveVertex (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativeUnitFiberElement A X))).val =
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectedPairing A).app (Opposite.op ⦋0⦌)
      ((nerveMap (simplicialElementsFiberFunctor (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A)
        (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointUnitIndex A X))).app _ (nerveVertex (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativeUnitFiberElement A X))) at h
  rw [hv] at h
  exact h

/-- 元のnative fiber射の単位の辺の類は、元のnative対象の恒等射。 -/
lemma strictBETotJointSourceNativeTwistedFiberMap_unit_arrow (X : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    Arrow.mk (HomotopyCategory.homMk (twistedArrowVertexEdge
      (((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativeTwistedFiberMap A (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointUnitIndex A X)).app
        (Opposite.op ⦋0⦌) (nerveVertex (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativeUnitFiberElement A X))).val))) =
      Arrow.mk (𝟙 (HomotopyCategory.mk ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A).app
        (Opposite.op ⦋0⦌) (nerveVertex (modelRelativeObject (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra X))))) := by
  have h := congrArg (fun v : (TwistedArrow (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A)) _⦋0⦌ =>
    Arrow.mk (HomotopyCategory.homMk (twistedArrowVertexEdge v))) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativeTwistedFiberMap_unit_value A X)
  exact h.trans (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectedPairing_unit_arrow A X)

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot

end
