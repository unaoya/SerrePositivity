module

public import SerrePositivity.EInfinity.SimplicialLocalization.HomMapLaws
public import SerrePositivity.EInfinity.SimplicialLocalization.KanEnrichedMap

/-!
# Kan 化した単体的局所化の係数関手則

概要：同じ Ex∞ による Kan 化が係数射の恒等・合成を保つことを証明する。
方針：元の固定 Hom の係数関手則を Ex∞ の関手則で送る。
規約：対象と元の Hom 作用を変更しない。
使われ方：coherent nerve の全係数関手性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.SimplicialLocalization

open CategoryTheory


/-- 概要：恒等相対関手は Kan 化後も恒等豊穣関手を誘導する（Dwyer–Kan）。
方針：元の Hom の恒等則と Ex∞ の恒等則を使う。
規約：同じ Kan 豊穣構造を保持する。
使われ方：局所化 nerve の係数の恒等則。 -/
lemma kanLocalizationEnrichedMap_id (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) :
    kanLocalizationEnrichedMap (𝟙 C) = EnrichedFunctor.id SSet (KanLocalizationObjects C) := by
  refine EnrichedFunctor.ext SSet (F := kanLocalizationEnrichedMap (𝟙 C))
    (G := EnrichedFunctor.id SSet (KanLocalizationObjects C)) (fun _ => rfl) ?_
  intro X Y
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (localizationHomMap (𝟙 C) X Y) ≫ 𝟙 _ = 𝟙 _
  rw [Category.comp_id, localizationHomMap_id, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map_id]

/-- 概要：相対関手の合成は Kan 化した豊穣係数射の合成を誘導する（Dwyer–Kan）。
方針：元の Hom の合成則と Ex∞ の合成則を使う。
規約：元の相対関手の合成順序を保持する。
使われ方：局所化 nerve の係数の合成則。 -/
lemma kanLocalizationEnrichedMap_comp {C D E : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}}
    (F : C ⟶ D) (G : D ⟶ E) :
    kanLocalizationEnrichedMap (F ≫ G) =
      (kanLocalizationEnrichedMap F).comp SSet (kanLocalizationEnrichedMap G) := by
  refine EnrichedFunctor.ext SSet (F := kanLocalizationEnrichedMap (F ≫ G))
    (G := (kanLocalizationEnrichedMap F).comp SSet (kanLocalizationEnrichedMap G))
    (fun _ => rfl) ?_
  intro X Y
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (localizationHomMap (F ≫ G) X Y) ≫ 𝟙 _ =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (localizationHomMap F X Y) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (localizationHomMap G (F.functor.obj X) (F.functor.obj Y))
  rw [Category.comp_id, localizationHomMap_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map_comp]

/-- 概要：Kan 化の同じ Hom 単位は相対係数射に自然（Dwyer–Kan）。
方針：実際の Ex∞ の単位の自然性を同じ固定 Hom 写像へ適用する。
規約：元の anodyne な単位を保持する。
使われ方：Kan 化前後の係数比較の可換正方形。 -/
lemma localizationHomKanUnit_naturality {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}} (F : C ⟶ D)
    (X Y : C.category) :
    localizationHomMap F X Y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (localizationHom D (F.functor.obj X) (F.functor.obj Y)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (localizationHom C X Y) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (localizationHomMap F X Y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.naturality (localizationHomMap F X Y)

end SerrePositivity.EInfinity.SimplicialLocalization
