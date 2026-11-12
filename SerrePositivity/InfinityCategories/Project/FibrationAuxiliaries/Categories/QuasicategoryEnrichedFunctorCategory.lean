module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedComparisonComposition

/-!
概要：全高次 Hom に自然な元の比較を射とする、quasicategory 値豊穣関手の通常圏。
方針：比較の同じ恒等・合成を使い、圏の法則を各成分で確認する。
規約：元の豊穣作用の全パラメーターを保持する。
使われ方：同じ比較の三辺を持つ三点図式を構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

/-- 元の quasicategory 値豊穣関手を対象とする圏の型。 -/
def QuasicategoryEnrichedFunctorCategory (C : Type v) [Category.{u} C] [SimplicialCategory C] :=
  EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u}

/-- 元の全高次比較の成分の恒等と合成による圏構造。 -/
instance quasicategoryEnrichedFunctorCategory_category
    (C : Type v) [Category.{u} C] [SimplicialCategory C] :
    Category (QuasicategoryEnrichedFunctorCategory C) where
  Hom F G := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedComparison F G
  id F := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedComparison.identity F
  comp η θ := η.trans θ
  id_comp η := by
    apply Subtype.ext
    funext X
    exact Category.id_comp (η.val X)
  comp_id η := by
    apply Subtype.ext
    funext X
    exact Category.comp_id (η.val X)
  assoc η θ ι := by
    apply Subtype.ext
    funext X
    exact Category.assoc (η.val X) (θ.val X) (ι.val X)

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
