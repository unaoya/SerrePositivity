module
public import SerrePositivity.KST.Fibration.KernelCofiberModel

/-! # W 辺と核に cofiber を持つ元の四角形

cofiber の選択を変えず、元の相対 cofiber 頂点条件を底辺の商での可逆性と同定する。
この判定を全 W 辺図式の全部分圏への比較に用いる。
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

/-- 元の cofiber 頂点の各角の評価は、同じ実四角形の頂点である。 -/
lemma cofiberVertex_corner (B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u})
    (v : (cofiberDiagrams B.obj) _⦋0⦌) (a : (Δ[1] ⊗ Δ[1] : SSet.{u}) _⦋0⦌) :
    (cofiberStableEvaluation (sInputModel B) a).val.app (Opposite.op ⦋0⦌) v =
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v.val).app (Opposite.op ⦋0⦌) a := by
  have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v.val) = v.val :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ B.obj).apply_symm_apply _
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a).app (Opposite.op ⦋0⦌) v.val = _
  exact (congrArg (fun w => (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := B.obj) a).app
    (Opposite.op ⦋0⦌) w) hv).symm.trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex a (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v.val))

/-- 元の全 cofiber 図式の頂点を、元の底辺の指定 cofiber として扱う。 -/
def vertexCofiberSquare {B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (v : (cofiberDiagrams B.obj) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v.val)) where
  square := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v.val
  zero_corner := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v).1
  bottom_edge := (SSet.yonedaEquiv.symm_apply_apply _).symm.trans
    (congrArg SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow_edge (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v.val)).symm)
  isPushout := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v).2

/-- E(C,C,ker q) の元の頂点条件は、同じ底辺の商像の可逆性と同値。 -/
lemma weakCofiber_predicate_iff_invertible
    {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (v : (cofiberDiagrams B.obj) _⦋0⦌) :
    (relativeCofiberPredicate (ClosedStablePredicate.top (sInputModel B))
      (kernelClosedPredicate q)).predicate v ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v.val)).map
        ((truncation 2).map q.hom)) := by
  change (True ∧ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (q.hom.app (Opposite.op ⦋0⦌)
    ((cofiberStableQuotient (sInputModel B)).val.app (Opposite.op ⦋0⦌) v))) ↔ _
  rw [true_and]
  have he := cofiberVertex_corner B v
    (stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm 1)
  change (cofiberStableQuotient (sInputModel B)).val.app (Opposite.op ⦋0⦌) v =
    (vertexCofiberSquare v).cofiber at he
  exact (congrArg (fun x => _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (q.hom.app (Opposite.op ⦋0⦌) x)) he).to_iff.trans
    ((vertexCofiberSquare v).map_isInvertible_iff_zero q.hom).symm

/-- 元の Verdier 列では相対 cofiber 図式の底辺は正確に W 辺である。 -/
lemma weakCofiber_predicate_iff_weakEquivalence
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (v : (cofiberDiagrams B.obj) _⦋0⦌) :
    (relativeCofiberPredicate (ClosedStablePredicate.top (sInputModel B))
      (kernelClosedPredicate q)).predicate v ↔
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v.val)).edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i :=
  (weakCofiber_predicate_iff_invertible q v).trans
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.mem_weakEquivalences_iff_invertible h _).symm

end SerrePositivity.KST.Fibration
