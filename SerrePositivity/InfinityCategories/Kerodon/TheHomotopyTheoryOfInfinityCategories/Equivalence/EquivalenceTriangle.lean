module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalDiagramRestriction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.InvertibleTriangleCancellation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.FullSubcomplexFibration

/-!
概要：同じ三辺が可逆な二単体を頂点とする、元の三角形の空間。
方針：元の関手空間の全部分複体を取り、同じ面を可逆 path へ制限する。
規約：全高次パラメーターと同じ二単体を保持する。
使われ方：元の比較三角形の Hom を、既存の可逆 path の Hom と比較する。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 三角形の関手頂点が表す、元の二単体。 -/
def triangleFunctorVertexSimplex {Y : SSet.{u}}
    (v : ((ihom (Δ[2] : SSet.{u})).obj Y) _⦋0⦌) : Y _⦋2⦌ :=
  SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[2] Y).symm v)

/-- 元の関手の頂点は、その元の同じ二単体を表す。 -/
lemma triangleFunctorVertexSimplex_functorVertex {Y : SSet.{u}} (f : (Δ[2] : SSet.{u}) ⟶ Y) :
    triangleFunctorVertexSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) = SSet.yonedaEquiv f := by
  change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[2] Y).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[2] Y f)) = _
  rw [Equiv.symm_apply_apply]

/-- 元の三角形の全ての辺が可逆であるという頂点条件。 -/
def IsEquivalenceTriangleVertex {Y : SSet.{u}}
    (v : ((ihom (Δ[2] : SSet.{u})).obj Y) _⦋0⦌) : Prop :=
  ∀ i : Fin 3, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (Y.δ i (triangleFunctorVertexSimplex v)))

/-- 同じ三辺が可逆な元の二単体からなる全部分複体。 -/
def equivalenceTriangle (Y : SSet.{u}) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (Δ[2] : SSet.{u})).obj Y) IsEquivalenceTriangleVertex

/-- 同じ元の三角形の全関手空間への包含。 -/
def equivalenceTriangleι (Y : SSet.{u}) :
    equivalenceTriangle Y ⟶ (ihom (Δ[2] : SSet.{u})).obj Y :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsEquivalenceTriangleVertex).ι

/-- 同じ三角形の各面は、元の同じ可逆 path を表す。 -/
lemma isEquivalencePathVertex_triangle_face {Y : SSet.{u}}
    (v : ((ihom (Δ[2] : SSet.{u})).obj Y) _⦋0⦌) (hv : IsEquivalenceTriangleVertex v)
    (i : Fin 3) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex (((pre (stdSimplex.δ i)).app Y).app (Opposite.op ⦋0⦌) v) := by
  obtain ⟨f, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[2] Y).surjective v
  have hi := hv i
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
    (Y.δ i (triangleFunctorVertexSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)))) at hi
  rw [triangleFunctorVertexSimplex_functorVertex] at hi
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge (((pre (stdSimplex.δ i)).app Y).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f))))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.functorVertex_precomposition, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_functorVertex,
    stdSimplex.yonedaEquiv_δ_comp]
  exact hi

/-- 同じ元の三角形の面を、既存の可逆 path の空間へ送る。 -/
def equivalenceTriangleFace (Y : SSet.{u}) (i : Fin 3) :
    equivalenceTriangle Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _ (equivalenceTriangleι Y ≫ (pre (stdSimplex.δ i)).app Y)
    (fun v ↦ isEquivalencePathVertex_triangle_face v.val (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v) i)

/-- 面の同じ比較は、包含後には元の二単体の制限そのもの。 -/
lemma equivalenceTriangleFace_ι (Y : SSet.{u}) (i : Fin 3) :
    equivalenceTriangleFace Y i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y =
      equivalenceTriangleι Y ≫ (pre (stdSimplex.δ i)).app Y := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

instance equivalenceTriangle_quasicategory (Y : SSet.{u}) [Quasicategory Y] :
    Quasicategory (equivalenceTriangle Y) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.fullSubcomplexOnVertices_quasicategory _ _

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
