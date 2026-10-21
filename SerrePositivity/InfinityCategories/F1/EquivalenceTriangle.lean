module

public import SerrePositivity.InfinityCategories.F1.IntervalDiagramRestriction
public import SerrePositivity.InfinityCategories.F1.InvertibleTriangleCancellation
public import SerrePositivity.InfinityCategories.Core.FullSubcomplexFibration

/-!
概要：同じ三辺が可逆な二単体を頂点とする、元の三角形の空間。
方針：元の関手空間の全部分複体を取り、同じ面を可逆 path へ制限する。
規約：全高次パラメーターと同じ二単体を保持する。
使われ方：元の比較三角形の Hom を、既存の可逆 path の Hom と比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 三角形の関手頂点が表す、元の二単体。 -/
def triangleFunctorVertexSimplex {Y : SSet.{u}}
    (v : ((ihom (Δ[2] : SSet.{u})).obj Y) _⦋0⦌) : Y _⦋2⦌ :=
  SSet.yonedaEquiv ((functorVertexEquiv Δ[2] Y).symm v)

/-- 元の関手の頂点は、その元の同じ二単体を表す。 -/
lemma triangleFunctorVertexSimplex_functorVertex {Y : SSet.{u}} (f : (Δ[2] : SSet.{u}) ⟶ Y) :
    triangleFunctorVertexSimplex (functorVertex f) = SSet.yonedaEquiv f := by
  change SSet.yonedaEquiv ((functorVertexEquiv Δ[2] Y).symm (functorVertexEquiv Δ[2] Y f)) = _
  rw [Equiv.symm_apply_apply]

/-- 元の三角形の全ての辺が可逆であるという頂点条件。 -/
def IsEquivalenceTriangleVertex {Y : SSet.{u}}
    (v : ((ihom (Δ[2] : SSet.{u})).obj Y) _⦋0⦌) : Prop :=
  ∀ i : Fin 3, IsInvertibleEdge (edgeOfSimplex (Y.δ i (triangleFunctorVertexSimplex v)))

/-- 同じ三辺が可逆な元の二単体からなる全部分複体。 -/
def equivalenceTriangle (Y : SSet.{u}) : SSet.{u} :=
  fullSubcomplexOnVertices ((ihom (Δ[2] : SSet.{u})).obj Y) IsEquivalenceTriangleVertex

/-- 同じ元の三角形の全関手空間への包含。 -/
def equivalenceTriangleι (Y : SSet.{u}) :
    equivalenceTriangle Y ⟶ (ihom (Δ[2] : SSet.{u})).obj Y :=
  (fullSubcomplexOnVertices _ IsEquivalenceTriangleVertex).ι

/-- 同じ三角形の各面は、元の同じ可逆 path を表す。 -/
lemma isEquivalencePathVertex_triangle_face {Y : SSet.{u}}
    (v : ((ihom (Δ[2] : SSet.{u})).obj Y) _⦋0⦌) (hv : IsEquivalenceTriangleVertex v)
    (i : Fin 3) : IsEquivalencePathVertex (((pre (stdSimplex.δ i)).app Y).app (Opposite.op ⦋0⦌) v) := by
  obtain ⟨f, rfl⟩ := (functorVertexEquiv Δ[2] Y).surjective v
  have hi := hv i
  change IsInvertibleEdge (edgeOfSimplex
    (Y.δ i (triangleFunctorVertexSimplex (functorVertex f)))) at hi
  rw [triangleFunctorVertexSimplex_functorVertex] at hi
  change IsInvertibleEdge (edgeOfSimplex
    (intervalFunctorVertexEdge (((pre (stdSimplex.δ i)).app Y).app _ (functorVertex f))))
  rw [functorVertex_precomposition, intervalFunctorVertexEdge_functorVertex,
    stdSimplex.yonedaEquiv_δ_comp]
  exact hi

/-- 同じ元の三角形の面を、既存の可逆 path の空間へ送る。 -/
def equivalenceTriangleFace (Y : SSet.{u}) (i : Fin 3) :
    equivalenceTriangle Y ⟶ equivalencePath Y :=
  fullSubcomplexLift _ (equivalenceTriangleι Y ≫ (pre (stdSimplex.δ i)).app Y)
    (fun v ↦ isEquivalencePathVertex_triangle_face v.val (fullSubcomplexOnVertices_vertex v) i)

/-- 面の同じ比較は、包含後には元の二単体の制限そのもの。 -/
lemma equivalenceTriangleFace_ι (Y : SSet.{u}) (i : Fin 3) :
    equivalenceTriangleFace Y i ≫ equivalencePathι Y =
      equivalenceTriangleι Y ≫ (pre (stdSimplex.δ i)).app Y := fullSubcomplexLift_ι _ _ _

instance equivalenceTriangle_quasicategory (Y : SSet.{u}) [Quasicategory Y] :
    Quasicategory (equivalenceTriangle Y) := fullSubcomplexOnVertices_quasicategory _ _

end SerrePositivity.InfinityCategories
