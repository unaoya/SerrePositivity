module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedComparison

/-!
概要：quasicategory 値豊穣関手の比較の恒等と合成。
方針：対象ごとの恒等と合成に豊穣自然性の可換式を適用する。
規約：全ての高次 Hom の自然性を保持する。
使われ方：比較の合成三角形を一つの通常の図式として実現する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

/-- 概要：豊穣関手の恒等比較。
方針：各対象で恒等射を取り評価の恒等則を使う。
規約：比較の成分は実際の恒等射。
使われ方：恒等を含む比較の列の実現。 -/
def QuasicategoryEnrichedComparison.identity {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (F : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u}) : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedComparison F F := by
  refine ⟨fun X ↦ 𝟙 (F.obj X), ?_⟩
  intro X Y
  change (𝟙 (F.obj X).obj ▷ SimplicialCategory.sHom X Y) ≫ uncurry (F.map X Y) =
    uncurry (F.map X Y) ≫ 𝟙 (F.obj Y).obj
  simp only [id_whiskerRight, Category.id_comp, Category.comp_id]

/-- 概要：二つの豊穣比較を全対象で同時に合成する。
方針：二つの豊穣自然性の可換式を順に適用する。
規約：合成の順は最初に η、次に θ。
使われ方：豊穣比較の合成を coherent な長辺として実現する。 -/
def QuasicategoryEnrichedComparison.trans {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {F G H : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u}}
    (η : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedComparison F G) (θ : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedComparison G H) :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedComparison F H := by
  refine ⟨fun X ↦ η.val X ≫ θ.val X, ?_⟩
  intro X Y
  change (((show (F.obj X).obj ⟶ (G.obj X).obj from η.val X) ≫
    (show (G.obj X).obj ⟶ (H.obj X).obj from θ.val X)) ▷
      SimplicialCategory.sHom X Y) ≫ uncurry (H.map X Y) =
    uncurry (F.map X Y) ≫ (show (F.obj Y).obj ⟶ (G.obj Y).obj from η.val Y) ≫
      (show (G.obj Y).obj ⟶ (H.obj Y).obj from θ.val Y)
  rw [comp_whiskerRight, Category.assoc, θ.property, ← Category.assoc, η.property,
    Category.assoc]

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
