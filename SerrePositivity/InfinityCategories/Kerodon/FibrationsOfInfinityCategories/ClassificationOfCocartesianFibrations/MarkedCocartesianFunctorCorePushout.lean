module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.MarkedCocartesianFunctorPushout
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.MarkedCocartesianFunctorRestrictionLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.CorePullbackRestriction

/-!
概要：指定辺を保つ元の Hom の core の、pushout に沿う厳密な貼り合わせ。
方針：単射による制限の同値持ち上げ性から inner fibration 性を得て core に移す。
規約：元の二つの制限そのものを pullback の射影にする。
使われ方：元の cocartesian Hom の区間の貼り合わせと高次セル比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 指定辺を覆う pushout は、同じ指定辺保存 Hom の実際の pullback を与える。 -/
lemma core_markedCocartesianFunctorPre_isPullback_of_isPushout
    {E B : SSet.{u}} [Quasicategory B] (q : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration q]
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
    IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPre q j W U hj))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPre q i V U hi))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPre q g A W hg))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPre q f A V hf)) := by
  letI : InnerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPre q g A W hg) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting.innerFibration
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEquivalenceLifting_markedCocartesianFunctorPre q g A W hg)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap_isPullback_of_isPullback
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPre_isPullback_of_isPushout q f g i j hp A V W U
      hf hg hi hj hcover)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
