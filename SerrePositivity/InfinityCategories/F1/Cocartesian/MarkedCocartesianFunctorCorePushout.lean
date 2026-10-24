module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.MarkedCocartesianFunctorPushout
public import SerrePositivity.InfinityCategories.F1.Cocartesian.MarkedCocartesianFunctorRestrictionLifting
public import SerrePositivity.InfinityCategories.F1.Categories.CorePullbackRestriction

/-!
概要：指定辺を保つ元の Hom の core の、pushout に沿う厳密な貼り合わせ。
方針：単射による制限の同値持ち上げ性から inner fibration 性を得て core に移す。
規約：元の二つの制限そのものを pullback の射影にする。
使われ方：元の cocartesian Hom の区間の貼り合わせと高次セル比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 指定辺を覆う pushout は、同じ指定辺保存 Hom の実際の pullback を与える。 -/
lemma core_markedCocartesianFunctorPre_isPullback_of_isPushout
    {E B : SSet.{u}} [Quasicategory B] (q : E ⟶ B) [CocartesianFibration q]
    {a b c d : Over B}
    (f : a ⟶ b) (g : a ⟶ c) (i : b ⟶ d) (j : c ⟶ d)
    [Mono g.left] (hp : IsPushout f.left g.left i.left j.left)
    (A : Set (a.left _⦋1⦌)) (V : Set (b.left _⦋1⦌))
    (W : Set (c.left _⦋1⦌)) (U : Set (d.left _⦋1⦌))
    (hf : ∀ e ∈ A, f.left.app (Opposite.op ⦋1⦌) e ∈ V)
    (hg : ∀ e ∈ A, g.left.app (Opposite.op ⦋1⦌) e ∈ W)
    (hi : ∀ e ∈ V, i.left.app (Opposite.op ⦋1⦌) e ∈ U)
    (hj : ∀ e ∈ W, j.left.app (Opposite.op ⦋1⦌) e ∈ U)
    (hcover : ∀ e ∈ U,
      (∃ v ∈ V, i.left.app (Opposite.op ⦋1⦌) v = e) ∨
      (∃ w ∈ W, j.left.app (Opposite.op ⦋1⦌) w = e)) :
    IsPullback (quasicategoryCoreMap (markedCocartesianFunctorPre q j W U hj))
      (quasicategoryCoreMap (markedCocartesianFunctorPre q i V U hi))
      (quasicategoryCoreMap (markedCocartesianFunctorPre q g A W hg))
      (quasicategoryCoreMap (markedCocartesianFunctorPre q f A V hf)) := by
  letI : InnerFibration (markedCocartesianFunctorPre q g A W hg) :=
    SerrePositivity.InfinityCategories.F1B.EquivalenceLifting.innerFibration
      (kanEquivalenceLifting_markedCocartesianFunctorPre q g A W hg)
  exact quasicategoryCoreMap_isPullback_of_isPullback
    (markedCocartesianFunctorPre_isPullback_of_isPushout q f g i j hp A V W U
      hf hg hi hj hcover)

end SerrePositivity.InfinityCategories
