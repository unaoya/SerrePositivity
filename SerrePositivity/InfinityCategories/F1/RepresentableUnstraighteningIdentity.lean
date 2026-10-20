module

public import SerrePositivity.InfinityCategories.F1.RepresentableUnstraighteningEvaluation
public import SerrePositivity.InfinityCategories.Stable.ColimitCoconeFamily

/-!
概要：Yoneda 評価で使った同じ恒等点を、実際の unstraightening 全空間の始対象として指定する。
方針：元の coslice の恒等錐を比較で送り、相対評価の前合成公式を全パラメーターで照合する。
規約：評価の選択に用いた比較を固定し、別の点への評価へ置き換えない。
使われ方：c1 の fiber 輸送比較と、実際の Yoneda 恒等点評価の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

local instance {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    Quasicategory (smallLeftUnstraightening (representablePresheafInfinity y)) :=
  quasicategory_of_innerFibration
    (smallLeftUnstraighteningProjection (representablePresheafInfinity y))

/-- 実際の Yoneda 評価が使う、左 unstraightening 全空間内の同じ恒等点。 -/
def representableUnstraighteningIdentity {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    (smallLeftUnstraightening (representablePresheafInfinity y)) _⦋0⦌ :=
  (representableCosliceUnstraighteningComparison y).app (Opposite.op ⦋0⦌)
    (cosliceIdentityCone (SSet.opObjEquiv.symm y))

/-- 同じ恒等点の射影は、指定した元の頂点。 -/
lemma representableUnstraighteningIdentity_projection
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    (smallLeftUnstraighteningProjection (representablePresheafInfinity y)).app
      (Opposite.op ⦋0⦌) (representableUnstraighteningIdentity y) = SSet.opObjEquiv.symm y := by
  have h := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌)
    (cosliceIdentityCone (SSet.opObjEquiv.symm y)))
    (representableCosliceUnstraighteningComparison_projection y)
  exact h.trans (cosliceIdentityCone_projection _)

/-- 同じ恒等点は、実際の左 unstraightening の全空間の始対象。 -/
lemma representableUnstraighteningIdentity_isInitialVertex
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    IsInitialVertex (representableUnstraighteningIdentity y) := by
  have hP := representableCosliceUnstraighteningComparison_isPrecompositionEquivalence y
  have h := hP.isQCatEquivalence
  exact h.choose.map_isInitialVertex (cosliceIdentityCone_isInitialVertex _)

/-- 元の全相対 Hom の Yoneda 評価は、同じ始対象における直接の評価そのもの。 -/
lemma representableUnstraighteningEvaluation_eq_identityEvaluation
    {E C : SSet.{u}} [Quasicategory C] (p : E ⟶ C.op) [LeftFibration p]
    (y : C _⦋0⦌) :
    representableUnstraighteningEvaluation p y =
      relativeFunctorEvaluate p
        (smallLeftUnstraighteningProjection (representablePresheafInfinity y))
        (representableUnstraighteningIdentity y) ≫
      eqToHom (congrArg (vertexFiber p) (representableUnstraighteningIdentity_projection y)) := by
  apply vertexFiber_hom_ext p (SSet.opObjEquiv.symm y)
  simp only [representableUnstraighteningEvaluation, Category.assoc]
  rw [vertexFiberTransport_ι p (cosliceIdentityCone_projection (SSet.opObjEquiv.symm y)),
    vertexFiberTransport_ι p (representableUnstraighteningIdentity_projection y)]
  rw [relativeFunctorEvaluate_ι, relativeFunctorEvaluate_ι, ← Category.assoc]
  have hi := relativeFunctorOverPre_ι p
    (Over.homMk
      (U := Over.mk (sliceUnderProjection
        (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm y))))
      (V := Over.mk (smallLeftUnstraighteningProjection (representablePresheafInfinity y)))
      (representableCosliceUnstraighteningComparison y)
      (representableCosliceUnstraighteningComparison_projection y))
  refine (congrArg (fun f ↦ f ≫
    evaluateFunctorAt (cosliceIdentityCone (SSet.opObjEquiv.symm y))) hi).trans ?_
  rw [Category.assoc, evaluateFunctorAt_pre]
  rfl

end SerrePositivity.InfinityCategories
