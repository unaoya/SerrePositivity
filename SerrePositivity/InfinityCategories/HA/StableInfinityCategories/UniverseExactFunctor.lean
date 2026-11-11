module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.UniverseStabilityDescent
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.ExactFunctor

/-! # 完全関手の宇宙降下

概要：単体集合の宇宙持ち上げで完全な関手は元の宇宙でも完全。
方針：零頂点と実四角形の押し出し性の保存・反映を使う。
規約：型やホモトピー圏の三角性に置き換えない。使われ方：dg 商関手の完全性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial

/-- 実四角形の持ち上げは実際の後合成と可換。 -/
lemma uliftSquare_postcomp {X Y : SSet.{u}}
    (L : Δ[1] ⊗ Δ[1] ⟶ X) (F : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquare.{u, v} (L ≫ F) =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquare.{u, v} L ≫ (SSet.uliftFunctor.{v, u}).map F := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquare, Functor.map_comp, Category.assoc]

/-- 零対象と cofiber 列の保存は持ち上げた宇宙から降下する。 -/
theorem isExactFunctor_of_ulift {X Y : SSet.{u}} (F : X ⟶ Y)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor ((SSet.uliftFunctor.{v, u}).map F)) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F where
  preservesZero x hx := by
    let := h
    exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isZeroVertex_iff_ulift.{u, v} _).2
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := (SSet.uliftFunctor.{v, u}).map F)
        (ULift.up x) ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isZeroVertex_iff_ulift.{u, v} x).1 hx))
  preservesCofiber t ht := by
    let := h
    apply (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isPushoutSquare_iff_ulift.{u, v} (t.square ≫ F)).2
    rw [uliftSquare_postcomp]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesCofiber (F := (SSet.uliftFunctor.{v, u}).map F)
      t.ulift ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isPushoutSquare_iff_ulift.{u, v} t.square).1 ht)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
