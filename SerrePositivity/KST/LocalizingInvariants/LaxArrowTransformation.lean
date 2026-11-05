module

public import SerrePositivity.KST.LocalizingInvariants.LaxStableCategory
public import SerrePositivity.InfinityCategories.Stable.Exact.ExactTransformationStableLocus
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackVertexData
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackEquivalenceSubcomplex

/-!
概要：lax pullback の指定矢印の全族を両完全射影の間の実自然変換と同定する。
方針：元の矢印射影を uncurry し、頂点の成分の一次単体と h の射の Arrow を照合する。
規約：元の指定矢印を保持する。使われ方：通常 pullback の安定閉性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

variable {C D E : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap D E)

def laxArrowHomotopy : SSet.Homotopy ((laxFst p q).hom ≫ p.hom)
    ((laxSnd p q).hom ≫ q.hom) where
  h := (β_ (laxCategory p q).obj (Δ[1] : SSet.{u})).hom ≫
    uncurry (F2.laxPullbackArrow p.hom q.hom)
  h₀ := by
    rw [← Category.assoc]
    change prismEndpoint 0 (laxCategory p q).obj ≫ uncurry _ = _
    rw [← curry_evaluateFunctorAt_interval, curry_uncurry]
    exact F2.laxPullbackArrow_source p.hom q.hom
  h₁ := by
    rw [← Category.assoc]
    change prismEndpoint 1 (laxCategory p q).obj ≫ uncurry _ = _
    rw [← curry_evaluateFunctorAt_interval, curry_uncurry]
    exact F2.laxPullbackArrow_target p.hom q.hom
  rel := by ext n ⟨x, y⟩; exact x.property.elim

lemma laxArrowHomotopy_component (x : (laxCategory p q).obj _⦋0⦌) :
    (simplicialHomotopyVertexEdge (laxArrowHomotopy p q) x).edge =
      (F2.laxPullbackVertexData p.hom q.hom x).arrow := by
  have h := intervalFunctorVertexEdge_curry
    (uncurry (F2.laxPullbackArrow p.hom q.hom)) x
  rw [curry_uncurry] at h
  change _ = intervalFunctorVertexEdge ((F2.laxPullbackArrow p.hom q.hom).app _ x)
  rw [h]
  change (uncurry (F2.laxPullbackArrow p.hom q.hom)).app (Opposite.op ⦋1⦌)
    (homotopyIntervalEdge.edge,
      (Truncated.Edge.id (X := (truncation 2).obj (laxCategory p q).obj) x).edge) = _
  rw [pinchedConstant_one]
  have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) = homotopyIntervalEdge.edge := by
    apply SSet.stdSimplex.ext
    intro i
    fin_cases i <;> rfl
  rw [hi]

lemma laxArrowTransformation_component (x : (laxCategory p q).obj _⦋0⦌) :
    Arrow.mk ((exactFunctorNatTrans (laxArrowHomotopy p q)).app (HomotopyCategory.mk x)) =
      Arrow.mk (Truncated.HomotopyCategory.homMk
        (edgeOfSimplex (F2.laxPullbackVertexData p.hom q.hom x).arrow)) := by
  change Arrow.mk ((homotopyNatTransOfEndpoints _ _ _).app _) = _
  rw [homotopyNatTransOfEndpoints_app_arrow, homotopyNatTrans_app]
  apply Truncated.HomotopyCategory.congr_arrowMk_homMk
  exact laxArrowHomotopy_component p q x

lemma laxEquivalenceVertex_iff_transformationIso (x : (laxCategory p q).obj _⦋0⦌) :
    F2.IsLaxEquivalenceVertex p.hom q.hom x ↔
      _root_.SerrePositivity.InfinityCategories.Stable.Exact.TransformationIsoVertex (laxArrowHomotopy p q) x := by
  exact (congrArg (fun a : Arrow (hoFunctor.obj E.obj) ↦ IsIso a.hom)
    (laxArrowTransformation_component p q x)).symm.to_iff

/-- 同値矢印の頂点条件は元の lax pullback の零・fiber・cofiber に閉じる。 -/
lemma laxEquivalenceVertex_stable :
    _root_.SerrePositivity.InfinityCategories.Stable.Exact.StableVertexCondition (F2.IsLaxEquivalenceVertex p.hom q.hom) := by
  let h := _root_.SerrePositivity.InfinityCategories.Stable.Exact.transformationIsoVertex_stable (laxArrowHomotopy p q)
  let e := laxEquivalenceVertex_iff_transformationIso p q
  exact {
    zero := fun x hx ↦ (e x).2 (h.zero x hx)
    cofiber := fun t ht ha hb ↦ (e _).2 (h.cofiber t ht ((e _).1 ha) ((e _).1 hb))
    fiber := fun t ht hb hc ↦ (e _).2 (h.fiber t ht ((e _).1 hb) ((e _).1 hc)) }

end SerrePositivity.KST.LocalizingInvariants
