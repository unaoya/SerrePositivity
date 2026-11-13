module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.WeightedColimitReindex
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.WeightedColimitWeightMap
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.WeightedColimit

/-!
概要：coend の添字変更は係数と重みの自然変換に自然。
方針：全ての普遍脚で各変数の作用を比較する。
規約：cofinality や余極限保存を仮定しない。
使われ方：Bousfield–Kan 添字変更の単位・合成・augmentation の整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

variable {I J K : Type u} [SmallCategory I] [SmallCategory J] [SmallCategory K]

/-- 概要：係数の自然変換と添字変更は可換。
方針：像での同じ成分が各普遍脚に作用することを使う。
規約：重みを固定する。使われ方：Bousfield–Kan 比較の図式に関する自然性。 -/
lemma weightedColimitReindex_map (W : Iᵒᵖ ⥤ SSet.{u}) {F G : I ⥤ SSet.{u}}
    (η : F ⟶ G) (U : J ⥤ I) :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitReindex W F U ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitMap W η =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitMap (U.op ⋙ W) (Functor.whiskerLeft U η) ≫
        _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitReindex W G U := by
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit_hom_ext
  intro j
  rw [reassoc_of% _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitι_reindex, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι_map,
    reassoc_of% _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι_map, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitι_reindex]
  rfl

/-- 概要：重みの自然変換と添字変更は可換。
方針：像での重みの同じ成分を各脚で比較する。
規約：係数図式を固定する。使われ方：添字変更の合成の重みの整合。 -/
lemma weightedColimitReindex_weightMap {W V : Iᵒᵖ ⥤ SSet.{u}} (μ : W ⟶ V)
    (F : I ⥤ SSet.{u}) (U : J ⥤ I) :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitReindex W F U ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitWeightMap μ F =
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitWeightMap (Functor.whiskerLeft U.op μ) (U ⋙ F) ≫
        _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitReindex V F U := by
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit_hom_ext
  intro j
  rw [reassoc_of% _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitι_reindex, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitι_weightMap,
    reassoc_of% _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitι_weightMap, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitι_reindex]
  rfl

/-- 概要：係数と重みの二つの変換の作用は可換。
方針：tensor の二変数の交換則を普遍脚で使う。
規約：両変換は元の指定されたもの。使われ方：coend の二変数での関手性。 -/
lemma weightedColimitWeightMap_map {W V : Iᵒᵖ ⥤ SSet.{u}} (μ : W ⟶ V)
    {F G : I ⥤ SSet.{u}} (η : F ⟶ G) :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitWeightMap μ F ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitMap V η =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitMap W η ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitWeightMap μ G := by
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit_hom_ext
  intro i
  rw [reassoc_of% _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitι_weightMap, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι_map,
    reassoc_of% _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι_map, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitι_weightMap]
  exact whisker_exchange_assoc _ _ _

/-- 概要：重みの比較を伴う二段の添字変更は合成関手による比較。
方針：添字変更と重み変更を交換して、それぞれの合成則を使う。
規約：三つの重みは任意。使われ方：Bousfield–Kan 添字変更の合成。 -/
lemma weightedColimitReindexWeightMap_comp
    {W : Iᵒᵖ ⥤ SSet.{u}} {V : Jᵒᵖ ⥤ SSet.{u}} {T : Kᵒᵖ ⥤ SSet.{u}}
    (F : I ⥤ SSet.{u}) (U : J ⥤ I) (L : K ⥤ J) (μ : V ⟶ U.op ⋙ W) (ν : T ⟶ L.op ⋙ V) :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitWeightMap ν (L ⋙ U ⋙ F) ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitReindex V (U ⋙ F) L ≫
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitWeightMap μ (U ⋙ F) ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitReindex W F U =
        _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitWeightMap (ν ≫ Functor.whiskerLeft L.op μ) (L ⋙ U ⋙ F) ≫
          _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitReindex W F (L ⋙ U) := by
  rw [reassoc_of% weightedColimitReindex_weightMap]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitWeightMap_comp]
  rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitReindex_comp]

end SerrePositivity.InfinityCategories.Project.FilteredExchange
