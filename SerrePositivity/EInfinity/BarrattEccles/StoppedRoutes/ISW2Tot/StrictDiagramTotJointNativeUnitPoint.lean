module

public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointNativeUnitFiber
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointHomInputVertex
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedHomVertexIsoOfArrowEq
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedHomIdentityPoint

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：同じnative単位点を元の恒等点へ、同じHom空間内の同型で結ぶ。
方針：底の既存の等式で係数を移し、元の辺の類の照合へR03iを適用する。
規約：元のnative fiber射・元の単位ラベル・元の恒等点を保持する。
使われ方：元の全straightening比較の単位評価の照合。
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory _root_.SSet _root_.HomotopicalAlgebra
open scoped _root_.Simplicial
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open _root_.SerrePositivity.EInfinity.BarrattEccles

noncomputable section

namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot

private lemma jointNativeUnitPointTransport_value {E B : SSet.{u}} (p : E ⟶ B) {b b' : B _⦋0⦌}
    (h : b = b') (n : SimplexCategoryᵒᵖ) (v : (vertexFiber p b).obj n) :
    ((eqToHom (congrArg (vertexFiber p) h)).app n v).val = v.val := by
  cases h
  rfl

variable (A : Type u) [CommRing A]
local instance jointNativeUnitPointModel : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A
local instance jointNativeUnitPointFactorization :
    (cofibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) := ⟨⟨_root_.SerrePositivity.EInfinity.BarrattEccles.mappingCofibrantFactorization A⟩⟩

/-- 元の入力の底の既存の等式だけを使い、同じ単位のfiberを同じHom空間へ合わせる。 -/
def strictBETotJointNativeUnitFiberIso (X : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    vertexFiber (twistedArrowProjection (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A))
      ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomInput A).app (Opposite.op ⦋0⦌)
        (nerveVertex (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointUnitIndex A X))) ≅
      twistedArrowHomSpace
        ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A).app (Opposite.op ⦋0⦌)
          (nerveVertex (modelRelativeObject (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra X)))
        ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A).app (Opposite.op ⦋0⦌)
          (nerveVertex (modelRelativeObject (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra X))) :=
  eqToIso (congrArg (vertexFiber (twistedArrowProjection (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A)))
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomInput_model_vertex A (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointUnitIndex A X)))

/-- 元のnative fiber射の同じ単位点を、底の同じ等式のfiber同型だけで移す。 -/
def strictBETotJointNativeUnitPoint (X : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    (twistedArrowHomSpace
      ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (modelRelativeObject (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra X)))
      ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (modelRelativeObject (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra X)))) _⦋0⦌ :=
  (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeUnitFiberIso A X).hom.app (Opposite.op ⦋0⦌)
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativeTwistedFiberMap A (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointUnitIndex A X)).app
      (Opposite.op ⦋0⦌) (nerveVertex (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativeUnitFiberElement A X)))

/-- 底の等式の係数移送後も、元のnative単位点の全空間での値は変わらない。 -/
lemma strictBETotJointNativeUnitPoint_value (X : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeUnitPoint A X).val =
      ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativeTwistedFiberMap A (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointUnitIndex A X)).app
        (Opposite.op ⦋0⦌) (nerveVertex (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativeUnitFiberElement A X))).val := by
  exact _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.jointNativeUnitPointTransport_value (twistedArrowProjection (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A))
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomInput_model_vertex A (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointUnitIndex A X)) _ _

/-- 元のnative単位点は、同じHom空間の元の始点固定の恒等点の像と同型。 -/
lemma strictBETotJointNativeUnitPoint_identityIso (X : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    Nonempty (VertexIso (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeUnitPoint A X)
      (twistedArrowHomSpaceIdentityPoint ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (modelRelativeObject (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra X))))) := by
  apply nonempty_twistedArrowHomSpace_vertexIso_of_arrow_eq
  have h := congrArg (fun v : (TwistedArrow (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A)) _⦋0⦌ =>
    Arrow.mk (HomotopyCategory.homMk (twistedArrowVertexEdge v)))
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeUnitPoint_value A X)
  exact (h.trans (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativeTwistedFiberMap_unit_arrow A X)).trans
    (twistedArrowHomSpaceIdentityPoint_arrow _).symm

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot

end
