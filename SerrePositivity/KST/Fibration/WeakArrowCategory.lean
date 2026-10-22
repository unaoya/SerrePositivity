module
public import SerrePositivity.KST.Fibration.WeakCofiberVertices
public import SerrePositivity.KST.Fibration.FullPredicateRestriction

/-! # W 辺の図式圏と全相対 cofiber 補完

商で可逆になる辺を対象とする全部分図式圏を作り、cofiber が核に属する全図式から
元の底辺を取る射を構成する。頂点条件の正確な逆像性から全境界持ち上げを保持する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 実辺の関手頂点から、同じ一次単体を回収する。 -/
def arrowVertexSimplex {B : SSet.{u}}
    (v : ((ihom (Δ[1] : SSet.{u})).obj B) _⦋0⦌) : B _⦋1⦌ :=
  SSet.yonedaEquiv ((functorVertexEquiv (Δ[1] : SSet.{u}) B).symm v)

/-- 商で可逆となる実辺の、図式圏内の頂点条件。 -/
def weakArrowPredicate {B C : StableCategory.{u}} (q : ExactMap B C)
    (v : ((ihom (Δ[1] : SSet.{u})).obj B.obj) _⦋0⦌) : Prop :=
  IsInvertibleEdge ((edgeOfSimplex (arrowVertexSimplex v)).map ((truncation 2).map q.hom))

/-- Verdier 列では、この図式圏の対象は元の W 辺に一致する。 -/
lemma weakArrowPredicate_iff_mem {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (v : ((ihom (Δ[1] : SSet.{u})).obj B.obj) _⦋0⦌) :
    weakArrowPredicate q v ↔ arrowVertexSimplex v ∈ weakEquivalences i :=
  (mem_weakEquivalences_iff_invertible h (edgeOfSimplex (arrowVertexSimplex v))).symm

/-- 全ての W 辺と、それらの間の全自然変換を持つ全部分 ∞ 圏。 -/
def weakArrowCategory {B C : StableCategory.{u}} (q : ExactMap B C) : SSet.{u} :=
  fullSubcomplexOnVertices ((ihom (Δ[1] : SSet.{u})).obj B.obj) (weakArrowPredicate q)

instance weakArrowCategory_quasicategory {B C : StableCategory.{u}} (q : ExactMap B C) :
    Quasicategory (weakArrowCategory q) :=
  inferInstanceAs (Quasicategory (fullSubcomplexOnVertices _ (weakArrowPredicate q) : SSet.{u}))

/-- 元の全 cofiber 射影は、同じ実四角形の底辺の一次単体を回収する。 -/
lemma cofiberProjection_vertex_simplex (B : StableCategory.{u})
    (v : (cofiberDiagrams B.obj) _⦋0⦌) :
    arrowVertexSimplex ((cofiberProjection B.obj).app (Opposite.op ⦋0⦌) v) =
      (squareBottomArrow (squareDiagram v.val)).edge := by
  have hv : functorVertex (squareDiagram v.val) = v.val :=
    (functorVertexEquiv _ B.obj).apply_symm_apply _
  have he : (functorVertexEquiv (Δ[1] : SSet.{u}) B.obj).symm
      ((cofiberProjection B.obj).app (Opposite.op ⦋0⦌) v) =
        squareBottomEdge ≫ squareDiagram v.val := by
    change (functorVertexEquiv (Δ[1] : SSet.{u}) B.obj).symm
      (((pre squareBottomEdge).app B.obj).app (Opposite.op ⦋0⦌) v.val) = _
    conv_lhs => rw [← hv]
    change (functorVertexEquiv (Δ[1] : SSet.{u}) B.obj).symm
      ((functorVertexEquiv (Δ[1] : SSet.{u}) B.obj)
        (squareBottomEdge ≫ squareDiagram v.val)) = _
    exact (functorVertexEquiv (Δ[1] : SSet.{u}) B.obj).symm_apply_apply
      (squareBottomEdge ≫ squareDiagram v.val)
  exact (congrArg SSet.yonedaEquiv he).trans
    (squareBottomArrow_edge (squareDiagram v.val)).symm

/-- 元の cofiber 射影による W 条件の逆像は、相対 cofiber の頂点条件そのもの。 -/
lemma weakCofiber_projection_predicate {B C : StableCategory.{u}} (q : ExactMap B C)
    (v : (cofiberDiagrams B.obj) _⦋0⦌) :
    (relativeCofiberPredicate (ClosedStablePredicate.top (sInputModel B))
      (kernelClosedPredicate q)).predicate v ↔
        weakArrowPredicate q ((cofiberProjection B.obj).app (Opposite.op ⦋0⦌) v) := by
  unfold weakArrowPredicate
  rw [cofiberProjection_vertex_simplex]
  exact (weakCofiber_predicate_iff_invertible q v).trans
    (isInvertibleEdge_congr
      (e := (squareBottomArrow (squareDiagram v.val)).map ((truncation 2).map q.hom))
      (f := (edgeOfSimplex (squareBottomArrow (squareDiagram v.val)).edge).map
        ((truncation 2).map q.hom)) rfl)

/-- 全相対 cofiber 補完を保持した、元の W 底辺への射影。 -/
def weakCofiberProjection {B C : StableCategory.{u}} (q : ExactMap B C) :
    (weakCofiberModel q).carrier ⟶ weakArrowCategory q :=
  fullPredicateMap (cofiberProjection B.obj)
    (relativeCofiberPredicate (ClosedStablePredicate.top (sInputModel B))
      (kernelClosedPredicate q)).predicate (weakArrowPredicate q)
    (fun v => (weakCofiber_projection_predicate q v).1)

/-- 射影を全部分圏に含めると、元の全 cofiber 図式の底辺射影を回収する。 -/
lemma weakCofiberProjection_ι {B C : StableCategory.{u}} (q : ExactMap B C) :
    weakCofiberProjection q ≫
      (fullSubcomplexOnVertices ((ihom (Δ[1] : SSet.{u})).obj B.obj)
        (weakArrowPredicate q)).ι =
      (relativeCofiberInclusion (ClosedStablePredicate.top (sInputModel B))
        (kernelClosedPredicate q)).val ≫ cofiberProjection B.obj := rfl

/-- W 辺への制限でも、全ての境界に対する cofiber 補完の持ち上げを保つ。 -/
instance weakCofiberProjection_trivialKanFibration {B C : StableCategory.{u}}
    (q : ExactMap B C) : TrivialKanFibration (weakCofiberProjection q) :=
  fullPredicateMap_trivialKanFibration (cofiberProjection B.obj) _ _
    (weakCofiber_projection_predicate q)

end SerrePositivity.KST.Fibration
