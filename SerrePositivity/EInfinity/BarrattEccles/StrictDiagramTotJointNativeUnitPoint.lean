module

public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointNativeUnitFiber
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointHomInputVertex
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedHomVertexIsoOfArrowEq
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedHomIdentityPoint

/-!
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
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet HomotopicalAlgebra
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.EInfinity.BarrattEccles

noncomputable section

namespace SerrePositivity.EInfinity.BarrattEccles

private lemma jointNativeUnitPointTransport_value {E B : SSet.{u}} (p : E ⟶ B) {b b' : B _⦋0⦌}
    (h : b = b') (n : SimplexCategoryᵒᵖ) (v : (vertexFiber p b).obj n) :
    ((eqToHom (congrArg (vertexFiber p) h)).app n v).val = v.val := by
  cases h
  rfl

variable (A : Type u) [CommRing A]
local instance jointNativeUnitPointModel : ModelCategory (operad A).Algebra := modelCategory A
local instance jointNativeUnitPointFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩

/-- 元の入力の底の既存の等式だけを使い、同じ単位のfiberを同じHom空間へ合わせる。 -/
def strictBETotJointNativeUnitFiberIso (X : (operad A).Algebra) :
    vertexFiber (twistedArrowProjection (CAlg_R A))
      ((strictBETotJointNativeHomInput A).app (Opposite.op ⦋0⦌)
        (nerveVertex (strictBETotJointUnitIndex A X))) ≅
      twistedArrowHomSpace
        ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
          (nerveVertex (modelRelativeObject (operad A).Algebra X)))
        ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
          (nerveVertex (modelRelativeObject (operad A).Algebra X))) :=
  eqToIso (congrArg (vertexFiber (twistedArrowProjection (CAlg_R A)))
    (strictBETotJointNativeHomInput_model_vertex A (strictBETotJointUnitIndex A X)))

/-- 元のnative fiber射の同じ単位点を、底の同じ等式のfiber同型だけで移す。 -/
def strictBETotJointNativeUnitPoint (X : (operad A).Algebra) :
    (twistedArrowHomSpace
      ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (modelRelativeObject (operad A).Algebra X)))
      ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (modelRelativeObject (operad A).Algebra X)))) _⦋0⦌ :=
  (strictBETotJointNativeUnitFiberIso A X).hom.app (Opposite.op ⦋0⦌)
    ((strictBETotJointSourceNativeTwistedFiberMap A (strictBETotJointUnitIndex A X)).app
      (Opposite.op ⦋0⦌) (nerveVertex (strictBETotJointSourceNativeUnitFiberElement A X)))

/-- 底の等式の係数移送後も、元のnative単位点の全空間での値は変わらない。 -/
lemma strictBETotJointNativeUnitPoint_value (X : (operad A).Algebra) :
    (strictBETotJointNativeUnitPoint A X).val =
      ((strictBETotJointSourceNativeTwistedFiberMap A (strictBETotJointUnitIndex A X)).app
        (Opposite.op ⦋0⦌) (nerveVertex (strictBETotJointSourceNativeUnitFiberElement A X))).val := by
  exact jointNativeUnitPointTransport_value (twistedArrowProjection (CAlg_R A))
    (strictBETotJointNativeHomInput_model_vertex A (strictBETotJointUnitIndex A X)) _ _

/-- 元のnative単位点は、同じHom空間の元の始点固定の恒等点の像と同型。 -/
lemma strictBETotJointNativeUnitPoint_identityIso (X : (operad A).Algebra) :
    Nonempty (VertexIso (strictBETotJointNativeUnitPoint A X)
      (twistedArrowHomSpaceIdentityPoint ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (modelRelativeObject (operad A).Algebra X))))) := by
  apply nonempty_twistedArrowHomSpace_vertexIso_of_arrow_eq
  have h := congrArg (fun v : (TwistedArrow (CAlg_R A)) _⦋0⦌ =>
    Arrow.mk (HomotopyCategory.homMk (twistedArrowVertexEdge v)))
      (strictBETotJointNativeUnitPoint_value A X)
  exact (h.trans (strictBETotJointSourceNativeTwistedFiberMap_unit_arrow A X)).trans
    (twistedArrowHomSpaceIdentityPoint_arrow _).symm

end SerrePositivity.EInfinity.BarrattEccles

end
