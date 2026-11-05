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
lemma cofiberVertex_corner (B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u})
    (v : (cofiberDiagrams B.obj) _⦋0⦌) (a : (Δ[1] ⊗ Δ[1] : SSet.{u}) _⦋0⦌) :
    (cofiberStableEvaluation (sInputModel B) a).val.app (Opposite.op ⦋0⦌) v =
      (squareDiagram v.val).app (Opposite.op ⦋0⦌) a := by
  have hv : functorVertex (squareDiagram v.val) = v.val :=
    (functorVertexEquiv _ B.obj).apply_symm_apply _
  change (evaluateFunctorAt a).app (Opposite.op ⦋0⦌) v.val = _
  exact (congrArg (fun w => (evaluateFunctorAt (Y := B.obj) a).app
    (Opposite.op ⦋0⦌) w) hv).symm.trans
      (evaluateFunctorAt_functorVertex a (squareDiagram v.val))

/-- 元の全 cofiber 図式の頂点を、元の底辺の指定 cofiber として扱う。 -/
def vertexCofiberSquare {B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (v : (cofiberDiagrams B.obj) _⦋0⦌) :
    CofiberSquare (squareBottomArrow (squareDiagram v.val)) where
  square := squareDiagram v.val
  zero_corner := (fullSubcomplexOnVertices_vertex v).1
  bottom_edge := (SSet.yonedaEquiv.symm_apply_apply _).symm.trans
    (congrArg SSet.yonedaEquiv.symm (squareBottomArrow_edge (squareDiagram v.val)).symm)
  isPushout := (fullSubcomplexOnVertices_vertex v).2

/-- E(C,C,ker q) の元の頂点条件は、同じ底辺の商像の可逆性と同値。 -/
lemma weakCofiber_predicate_iff_invertible
    {B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C) (v : (cofiberDiagrams B.obj) _⦋0⦌) :
    (relativeCofiberPredicate (ClosedStablePredicate.top (sInputModel B))
      (kernelClosedPredicate q)).predicate v ↔
      IsInvertibleEdge ((squareBottomArrow (squareDiagram v.val)).map
        ((truncation 2).map q.hom)) := by
  change (True ∧ IsZeroVertex (q.hom.app (Opposite.op ⦋0⦌)
    ((cofiberStableQuotient (sInputModel B)).val.app (Opposite.op ⦋0⦌) v))) ↔ _
  rw [true_and]
  have he := cofiberVertex_corner B v
    (stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm 1)
  change (cofiberStableQuotient (sInputModel B)).val.app (Opposite.op ⦋0⦌) v =
    (vertexCofiberSquare v).cofiber at he
  exact (congrArg (fun x => IsZeroVertex (q.hom.app (Opposite.op ⦋0⦌) x)) he).to_iff.trans
    ((vertexCofiberSquare v).map_isInvertible_iff_zero q.hom).symm

/-- 元の Verdier 列では相対 cofiber 図式の底辺は正確に W 辺である。 -/
lemma weakCofiber_predicate_iff_weakEquivalence
    {A B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i q) (v : (cofiberDiagrams B.obj) _⦋0⦌) :
    (relativeCofiberPredicate (ClosedStablePredicate.top (sInputModel B))
      (kernelClosedPredicate q)).predicate v ↔
      (squareBottomArrow (squareDiagram v.val)).edge ∈ _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i :=
  (weakCofiber_predicate_iff_invertible q v).trans
    (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.mem_weakEquivalences_iff_invertible h _).symm

end SerrePositivity.KST.Fibration
