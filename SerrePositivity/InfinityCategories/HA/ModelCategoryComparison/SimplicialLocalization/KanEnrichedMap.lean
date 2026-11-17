module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.EnrichedMap
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanEnrichment

/-!
# 単体的局所化の係数射の Kan 化

概要：Dwyer–Kan の豊穣係数関手を同じ有限積保存 Ex∞ で送る。
方針：元の Hom 作用を Ex∞ で送り、tensorator の自然性で合成則を照合する。
規約：対象と元の係数関手を保持し、単体集合モデルを入力しない。
使われ方：coherent nerve の間の係数 ∞ 関手。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory


/-- 概要：相対関手は Kan 化した局所化の豊穣関手を与える（Dwyer–Kan）。
方針：同じ Ex∞ の関手則と tensorator の自然性を使う。
規約：各 Hom の作用は元の係数射の Ex∞ 像そのもの。
使われ方：Kan な局所化の coherent nerve への後合成。 -/
def kanLocalizationEnrichedMap {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}} (F : C ⟶ D) :
    EnrichedFunctor SSet.{u} (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanLocalizationObjects C) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanLocalizationObjects D) where
  obj := F.functor.obj
  map X Y := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHomMap F X Y)
  map_id X := by
    change (Functor.LaxMonoidal.ε _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationIdentity C X)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHomMap F X X) =
        Functor.LaxMonoidal.ε _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationIdentity D (F.functor.obj X))
    have hi : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationIdentity C X ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHomMap F X X =
        _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationIdentity D (F.functor.obj X) :=
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationEnrichedMap F).map_id (show _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.LocalizationObjects C from X)
    rw [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map_comp, hi]
  map_comp X Y Z := by
    change (Functor.LaxMonoidal.μ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _ _ ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationComposition C X Y Z)) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHomMap F X Z) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHomMap F X Y) ⊗ₘ
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHomMap F Y Z)) ≫
          Functor.LaxMonoidal.μ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _ _ ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationComposition D (F.functor.obj X)
              (F.functor.obj Y) (F.functor.obj Z))
    have hc : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationComposition C X Y Z ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHomMap F X Z =
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHomMap F X Y ⊗ₘ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHomMap F Y Z) ≫
          _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationComposition D (F.functor.obj X) (F.functor.obj Y) (F.functor.obj Z) :=
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationEnrichedMap F).map_comp (show _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.LocalizationObjects C from X)
        (show _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.LocalizationObjects C from Y) (show _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.LocalizationObjects C from Z)
    rw [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map_comp, hc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map_comp, ← Category.assoc, ← Functor.LaxMonoidal.μ_natural,
      Category.assoc]

/-- 概要：Kan 化した同じ豊穣係数射の基礎関手（Dwyer–Kan）。
方針：同じ ForgetEnrichment の標準関手を使う。
規約：同じ Kan Hom への作用を保持する。
使われ方：局所 Kan な単体的圏の係数比較。 -/
def kanLocalizationFunctor {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}} (F : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanLocalizationCategory C ⥤ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanLocalizationCategory D :=
  (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanLocalizationEnrichedMap F).forget

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
