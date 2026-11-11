module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FiniteHoDenominators

/-! # 分母の後で一致する有限族の同時均等化

概要：それぞれ分母の後で一致する有限族の二射を、一つの分母の前合成で同時に一致させる。
方針：右分数計算の均等化を各対に適用し、得た分母の共通分母を取る。
規約：各対の終域は異なってよい。使われ方：実分数表示の有限比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory SSet
open scoped _root_.Simplicial
variable {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]

/-- 分母での後合成後に一致する有限族は、一つの分母で同時に前から一致させられる。 -/
theorem stableHoClosure_equalizeFinite (P : Set (X _⦋0⦌))
    {n : ℕ} {x : hoFunctor.obj X} {y z : Fin n → hoFunctor.obj X}
    (f g : ∀ i, x ⟶ y i) (s : ∀ i, y i ⟶ z i)
    (hs : ∀ i, (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure P).trW (s i))
    (h : ∀ i, f i ≫ s i = g i ≫ s i) :
    ∃ (q : hoFunctor.obj X) (t : q ⟶ x), (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure P).trW t ∧
      ∀ i, t ≫ f i = t ≫ g i := by
  choose q t ht he using fun i =>
    MorphismProperty.HasRightCalculusOfFractions.ext (W := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure P).trW)
      (f i) (g i) (s i) (hs i) (h i)
  obtain ⟨q', t', ht', r, hr⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure_commonDenominator P q t ht
  refine ⟨q', t', ht', fun i => ?_⟩
  rw [← hr i, Category.assoc, he i, ← Category.assoc]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
