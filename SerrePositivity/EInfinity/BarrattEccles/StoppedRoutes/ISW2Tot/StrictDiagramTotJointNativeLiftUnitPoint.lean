module

public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointNativeLiftUnit
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointNativeUnitPoint

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：元の置換単位を保つ同じ全空間の射の実fiberで、単位点の像を照合する。
方針：元の全写像の単位条件と同じfiber単位の厳密な式を、R03iの同じ単位点の比較へ合成する。
規約：元の単位条件だけを使い、射の弱同値性は仮定しない。
使われ方：元のnative全変換の指定単位の評価。
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open _root_.CategoryTheory _root_.SSet _root_.HomotopicalAlgebra
open _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open scoped _root_.Simplicial
open _root_.SerrePositivity.EInfinity.BarrattEccles
open _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

noncomputable section

namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot

variable (A : Type u) [CommRing A]
local instance jointNativeLiftUnitPointModel : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A
local instance jointNativeLiftUnitPointFactorization :
    (cofibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) := ⟨⟨_root_.SerrePositivity.EInfinity.BarrattEccles.mappingCofibrantFactorization A⟩⟩

/-- 元の置換単位を保つ同じ全空間の射は、同じ実fiberの単位点を元の恒等点と同型な点へ送る。 -/
lemma strictBETotJointSourceNativeLiftUnit_identityPoint
    (m : (simplicialElementsReplacement (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A)).left ⟶
      _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomTotalSpace A)
    (hm : m ≫ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomProjection A =
      (simplicialElementsReplacement (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A)).hom)
    (hu : ((continuousLeftFibrationReplacementUnit (nerve (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A))).app
      (Over.mk (nerveMap (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceElementsProjection A)))).left ≫ m =
        _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativeHomMap A) (X : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    let P := _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointUnitIndex A X
    Nonempty (VertexIso
      ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeUnitFiberIso A X).hom.app (Opposite.op ⦋0⦌)
        (((simplicialElementsFiberUnit (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A) P ≫
          vertexFiberMap (simplicialElementsReplacement (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A)).hom
            (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomProjection A) m hm (nerveVertex P) ≫
          (vertexFiberPullbackIso (twistedArrowProjection (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A))
            (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomInput A) (nerveVertex P)).hom).app (Opposite.op ⦋0⦌)
              (nerveVertex (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativeUnitFiberElement A X)))))
      (twistedArrowHomSpaceIdentityPoint ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (modelRelativeObject (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra X))))) := by
  dsimp only
  have h := congrArg (fun f :
      nerve ((simplicialElementsCatDiagram (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A)).obj
        (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointUnitIndex A X)) ⟶
          vertexFiber (twistedArrowProjection (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A))
            ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomInput A).app (Opposite.op ⦋0⦌)
              (nerveVertex (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointUnitIndex A X))) =>
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeUnitFiberIso A X).hom.app (Opposite.op ⦋0⦌)
      (f.app (Opposite.op ⦋0⦌) (nerveVertex (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativeUnitFiberElement A X))))
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativeLiftUnit_twistedFiberMap A m hm hu (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointUnitIndex A X))
  change _ = _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeUnitPoint A X at h
  rw [h]
  exact _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeUnitPoint_identityIso A X

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot

end
