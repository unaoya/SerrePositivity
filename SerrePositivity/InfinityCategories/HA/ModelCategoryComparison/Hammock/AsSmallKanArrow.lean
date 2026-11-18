module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallArrow
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ExInfinityEnrichedUnit

/-!
概要：元の Kan hammock の宇宙比較は元の射の零単体を同じ持ち上げた射へ送る。
方針：同じ Ex∞ 単位の自然性と元の AsSmall 射の全単体公式を使う。
規約：実射の厳密な等式、反転後の代替比較へ置換しない。
使われ方：S (7) の実全自然比較の零単体回収。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison
open _root_.CategoryTheory _root_.SSet _root_.CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  {X Y : C}

/-- 概要：同じ実 Kan Hom 比較は元の射の零単体の全一定単体を厳密に保持する。
方針：元の Ex∞ 単位の自然性と同じ宇宙比較の元の forward 射の公式を合成する。
規約：同じ全自然変換の実成分。
使われ方：Yoneda 比較へ渡す元の射の零単体の同定。 -/
lemma arrowMap_exInfinity_colimitIso (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison.colimitIso W X Y).hom =
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison.weak W) (AsSmall.up.map f) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison.weak W) (AsSmall.up.obj X) (AsSmall.up.obj Y)) := by
  have h := congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W f ≫ ·) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.naturality (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison.colimitIso W X Y).hom)
  simp only [Functor.id_map] at h
  exact h.symm.trans (by
    simpa only [Category.assoc] using congrArg
      (fun a => a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison.weak W) (AsSmall.up.obj X) (AsSmall.up.obj Y)))
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison.arrowMap_colimitIso W f))

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison
