module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitGraph

/-!
# 全語の単体集合の余極限の元の点の表示

概要：各次数の余極限の点は元のある固定語の単体の像である。
方針：評価関手の余極限保存と型の余極限の共同全射性を使う。
規約：添字の filtered 性は不要。
使われ方：非空部分の像の判定と切断の反復。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u
noncomputable section
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory CategoryTheory.Limits

lemma colimit_point_surjective (F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ SSet.{u}) (n : SimplexCategoryᵒᵖ)
    (x : (colimit F).obj n) : ∃ w τ, (colimit.ι F w).app n τ = x := by
  exact Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves ((evaluation _ (Type u)).obj n) (colimit.isColimit F)) x

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
