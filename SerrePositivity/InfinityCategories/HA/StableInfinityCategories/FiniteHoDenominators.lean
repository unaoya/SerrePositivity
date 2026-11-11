module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberHoDenominators

/-! # 有限族の共通 Verdier 分母

概要：h C の有限個の分母は一つの共通分母で同時に細分できる。
方針：実安定閉包の三角的分母に右分数計算を適用し、有限族で帰納する。
規約：高次の境界条件を持つ coherent 分数表示は別途必要。使われ方：実辺への持ち上げ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory SSet
open scoped _root_.Simplicial
variable {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]

/-- 有限個の同じ終域を持つ Verdier 分母は、同じ分母を通じて同時に因子分解する。 -/
theorem stableHoClosure_commonDenominator (P : Set (X _⦋0⦌))
    {n : ℕ} {x : hoFunctor.obj X} (y : Fin n → hoFunctor.obj X)
    (s : ∀ i, y i ⟶ x) (hs : ∀ i, (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure P).trW (s i)) :
    ∃ (q : hoFunctor.obj X) (t : q ⟶ x), (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure P).trW t ∧
      ∃ r : ∀ i, q ⟶ y i, ∀ i, r i ≫ s i = t := by
  induction n with
  | zero =>
    exact ⟨x, 𝟙 x, MorphismProperty.id_mem _ x, (fun i => Fin.elim0 i),
      (fun i => Fin.elim0 i)⟩
  | succ n ih =>
    obtain ⟨q, t, ht, r, hr⟩ := ih (fun i => y i.succ) (fun i => s i.succ)
      (fun i => hs i.succ)
    let φ : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure P).trW.LeftFraction q (y 0) := ⟨t, s 0, hs 0⟩
    obtain ⟨ψ, hψ⟩ := φ.exists_rightFraction
    refine ⟨ψ.X', ψ.s ≫ t, MorphismProperty.comp_mem _ _ _ ψ.hs ht,
      Fin.cases ψ.f (fun i => ψ.s ≫ r i), ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hψ.symm
    · change (ψ.s ≫ r j) ≫ s j.succ = ψ.s ≫ t
      rw [Category.assoc, hr j]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
