module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.WeightedColimitWeightMap

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
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {I J K : Type u} [SmallCategory I] [SmallCategory J] [SmallCategory K]

/-- 概要：係数の自然変換と添字変更は可換。
方針：像での同じ成分が各普遍脚に作用することを使う。
規約：重みを固定する。使われ方：Bousfield–Kan 比較の図式に関する自然性。 -/
lemma weightedColimitReindex_map (W : Iᵒᵖ ⥤ SSet.{u}) {F G : I ⥤ SSet.{u}}
    (η : F ⟶ G) (U : J ⥤ I) :
    weightedColimitReindex W F U ≫ weightedColimitMap W η =
      weightedColimitMap (U.op ⋙ W) (Functor.whiskerLeft U η) ≫
        weightedColimitReindex W G U := by
  apply weightedColimit_hom_ext
  intro j
  rw [reassoc_of% weightedColimitι_reindex, weightedColimitι_map,
    reassoc_of% weightedColimitι_map, weightedColimitι_reindex]
  rfl

/-- 概要：重みの自然変換と添字変更は可換。
方針：像での重みの同じ成分を各脚で比較する。
規約：係数図式を固定する。使われ方：添字変更の合成の重みの整合。 -/
lemma weightedColimitReindex_weightMap {W V : Iᵒᵖ ⥤ SSet.{u}} (μ : W ⟶ V)
    (F : I ⥤ SSet.{u}) (U : J ⥤ I) :
    weightedColimitReindex W F U ≫ weightedColimitWeightMap μ F =
      weightedColimitWeightMap (Functor.whiskerLeft U.op μ) (U ⋙ F) ≫
        weightedColimitReindex V F U := by
  apply weightedColimit_hom_ext
  intro j
  rw [reassoc_of% weightedColimitι_reindex, weightedColimitι_weightMap,
    reassoc_of% weightedColimitι_weightMap, weightedColimitι_reindex]
  rfl

/-- 概要：係数と重みの二つの変換の作用は可換。
方針：tensor の二変数の交換則を普遍脚で使う。
規約：両変換は元の指定されたもの。使われ方：coend の二変数での関手性。 -/
lemma weightedColimitWeightMap_map {W V : Iᵒᵖ ⥤ SSet.{u}} (μ : W ⟶ V)
    {F G : I ⥤ SSet.{u}} (η : F ⟶ G) :
    weightedColimitWeightMap μ F ≫ weightedColimitMap V η =
      weightedColimitMap W η ≫ weightedColimitWeightMap μ G := by
  apply weightedColimit_hom_ext
  intro i
  rw [reassoc_of% weightedColimitι_weightMap, weightedColimitι_map,
    reassoc_of% weightedColimitι_map, weightedColimitι_weightMap]
  exact whisker_exchange_assoc _ _ _

/-- 概要：重みの比較を伴う二段の添字変更は合成関手による比較。
方針：添字変更と重み変更を交換して、それぞれの合成則を使う。
規約：三つの重みは任意。使われ方：Bousfield–Kan 添字変更の合成。 -/
lemma weightedColimitReindexWeightMap_comp
    {W : Iᵒᵖ ⥤ SSet.{u}} {V : Jᵒᵖ ⥤ SSet.{u}} {T : Kᵒᵖ ⥤ SSet.{u}}
    (F : I ⥤ SSet.{u}) (U : J ⥤ I) (L : K ⥤ J) (μ : V ⟶ U.op ⋙ W) (ν : T ⟶ L.op ⋙ V) :
    weightedColimitWeightMap ν (L ⋙ U ⋙ F) ≫ weightedColimitReindex V (U ⋙ F) L ≫
      weightedColimitWeightMap μ (U ⋙ F) ≫ weightedColimitReindex W F U =
        weightedColimitWeightMap (ν ≫ Functor.whiskerLeft L.op μ) (L ⋙ U ⋙ F) ≫
          weightedColimitReindex W F (L ⋙ U) := by
  rw [reassoc_of% weightedColimitReindex_weightMap]
  rw [← Category.assoc, weightedColimitWeightMap_comp]
  rw [weightedColimitReindex_comp]

end SerrePositivity.InfinityCategories.F2
