module
public import SerrePositivity.KST.SConstruction.CutSupportPredicates
public import SerrePositivity.KST.SConstruction.CutStableComparison

/-! # 切断の両端の支持条件
概要：min・max による切断の両端が、それぞれ左支持・右支持に入ることを実証明する。
方針：反対側の区間は元の (k,k) の評価に厳密に潰れる。
規約：部分圏への所属を追加仮定にしない。使われ方：相対 cofiber への切断比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- min による切断の左側の像は左支持条件を満たす。 -/
lemma cutLeftSupport_sMap (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u})
    (v : (sConstruction n X.carrier) _⦋0⦌) :
    (cutLeftSupport n k X).predicate
      ((sMap X.carrier (cutCornerOrder k 0 0)).app (Opposite.op ⦋0⦌) v) := by
  intro a
  have ha : (arNerveMap (cutCornerOrder k 0 0)).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ a.val) = ComposableArrows.mk₀ (arObj k k le_rfl) := by
    apply ComposableArrows.ext₀
    apply ULift.ext
    apply Subtype.ext
    apply Prod.ext
    · exact (cutEndpoint_zero_zero k a.val.down.val.1).trans (min_eq_right a.property)
    · exact (cutEndpoint_zero_zero k a.val.down.val.2).trans
        (min_eq_right (a.property.trans a.val.down.property))
  have he := sMap_evaluate_vertex (cutCornerOrder k 0 0) v (ComposableArrows.mk₀ a.val)
  have hz : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      ((arNerveMap (cutCornerOrder k 0 0)).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ a.val))).app
        (Opposite.op ⦋0⦌) v.val) := by
    rw [ha]
    exact sConstructionVertex_diagonal_isZero v k
  exact (congrArg _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex he).mpr hz

/-- max による切断の右側の像は右支持条件を満たす。 -/
lemma cutRightSupport_sMap (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u})
    (v : (sConstruction n X.carrier) _⦋0⦌) :
    (cutRightSupport n k X).predicate
      ((sMap X.carrier (cutCornerOrder k 1 1)).app (Opposite.op ⦋0⦌) v) := by
  intro a
  have ha : (arNerveMap (cutCornerOrder k 1 1)).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ a.val) = ComposableArrows.mk₀ (arObj k k le_rfl) := by
    apply ComposableArrows.ext₀
    apply ULift.ext
    apply Subtype.ext
    apply Prod.ext
    · exact (cutEndpoint_one_one k a.val.down.val.1).trans
        (max_eq_right (a.val.down.property.trans a.property))
    · exact (cutEndpoint_one_one k a.val.down.val.2).trans (max_eq_right a.property)
  have he := sMap_evaluate_vertex (cutCornerOrder k 1 1) v (ComposableArrows.mk₀ a.val)
  have hz : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      ((arNerveMap (cutCornerOrder k 1 1)).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ a.val))).app
        (Opposite.op ⦋0⦌) v.val) := by
    rw [ha]
    exact sConstructionVertex_diagonal_isZero v k
  exact (congrArg _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex he).mpr hz

end SerrePositivity.KST.SConstruction
