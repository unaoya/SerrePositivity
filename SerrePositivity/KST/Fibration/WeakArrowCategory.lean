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
  SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[1] : SSet.{u}) B).symm v)

/-- 商で可逆となる実辺の、図式圏内の頂点条件。 -/
def weakArrowPredicate {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    (v : ((ihom (Δ[1] : SSet.{u})).obj B.obj) _⦋0⦌) : Prop :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (arrowVertexSimplex v)).map ((truncation 2).map q.hom))

/-- Verdier 列では、この図式圏の対象は元の W 辺に一致する。 -/
lemma weakArrowPredicate_iff_mem {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C} (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)
    (v : ((ihom (Δ[1] : SSet.{u})).obj B.obj) _⦋0⦌) :
    weakArrowPredicate q v ↔ arrowVertexSimplex v ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i :=
  (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.mem_weakEquivalences_iff_invertible h (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (arrowVertexSimplex v))).symm

/-- 全ての W 辺と、それらの間の全自然変換を持つ全部分 ∞ 圏。 -/
def weakArrowCategory {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (Δ[1] : SSet.{u})).obj B.obj) (weakArrowPredicate q)

instance weakArrowCategory_quasicategory {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    Quasicategory (weakArrowCategory q) :=
  inferInstanceAs (Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakArrowPredicate q) : SSet.{u}))

/-- 元の全 cofiber 射影は、同じ実四角形の底辺の一次単体を回収する。 -/
lemma cofiberProjection_vertex_simplex (B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u})
    (v : (cofiberDiagrams B.obj) _⦋0⦌) :
    arrowVertexSimplex ((cofiberProjection B.obj).app (Opposite.op ⦋0⦌) v) =
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v.val)).edge := by
  have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v.val) = v.val :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ B.obj).apply_symm_apply _
  have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[1] : SSet.{u}) B.obj).symm
      ((cofiberProjection B.obj).app (Opposite.op ⦋0⦌) v) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v.val := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[1] : SSet.{u}) B.obj).symm
      (((pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge).app B.obj).app (Opposite.op ⦋0⦌) v.val) = _
    conv_lhs => rw [← hv]
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[1] : SSet.{u}) B.obj).symm
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[1] : SSet.{u}) B.obj)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v.val)) = _
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[1] : SSet.{u}) B.obj).symm_apply_apply
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v.val)
  exact (congrArg SSet.yonedaEquiv he).trans
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow_edge (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v.val)).symm

/-- 元の cofiber 射影による W 条件の逆像は、相対 cofiber の頂点条件そのもの。 -/
lemma weakCofiber_projection_predicate {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    (v : (cofiberDiagrams B.obj) _⦋0⦌) :
    (relativeCofiberPredicate (ClosedStablePredicate.top (sInputModel B))
      (kernelClosedPredicate q)).predicate v ↔
        weakArrowPredicate q ((cofiberProjection B.obj).app (Opposite.op ⦋0⦌) v) := by
  unfold weakArrowPredicate
  rw [cofiberProjection_vertex_simplex]
  exact (weakCofiber_predicate_iff_invertible q v).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
      (e := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v.val)).map ((truncation 2).map q.hom))
      (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v.val)).edge).map
        ((truncation 2).map q.hom)) rfl)

/-- 全相対 cofiber 補完を保持した、元の W 底辺への射影。 -/
def weakCofiberProjection {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    (weakCofiberModel q).carrier ⟶ weakArrowCategory q :=
  fullPredicateMap (cofiberProjection B.obj)
    (relativeCofiberPredicate (ClosedStablePredicate.top (sInputModel B))
      (kernelClosedPredicate q)).predicate (weakArrowPredicate q)
    (fun v => (weakCofiber_projection_predicate q v).1)

/-- 射影を全部分圏に含めると、元の全 cofiber 図式の底辺射影を回収する。 -/
lemma weakCofiberProjection_ι {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    weakCofiberProjection q ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (Δ[1] : SSet.{u})).obj B.obj)
        (weakArrowPredicate q)).ι =
      (relativeCofiberInclusion (ClosedStablePredicate.top (sInputModel B))
        (kernelClosedPredicate q)).val ≫ cofiberProjection B.obj := rfl

/-- W 辺への制限でも、全ての境界に対する cofiber 補完の持ち上げを保つ。 -/
instance weakCofiberProjection_trivialKanFibration {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (weakCofiberProjection q) :=
  fullPredicateMap_trivialKanFibration (cofiberProjection B.obj) _ _
    (weakCofiber_projection_predicate q)

end SerrePositivity.KST.Fibration
