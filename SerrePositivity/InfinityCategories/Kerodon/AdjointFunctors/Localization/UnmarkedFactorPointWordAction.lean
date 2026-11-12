module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorPointIndex
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorColimitImages

/-!
# 元の切断点と全語の作用

概要：圧縮・恒等列の挿入の前後で、依存和の実際の切断点が等しいことを証明する。
方針：像の最小列での因子の標準射の比較と元の最小列の回収を結合する。
規約：指定 prefix の実際の W-hammock と残りの元の余極限を使う。
使われ方：切断の全語の自然な余錐と余極限への降下。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ}
  (f : a ⟶ b) (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths a X Y).obj n) (h : ∃ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj 0) j ≠ [])
  (hf : ∃ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W ((τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f).obj 0) j ≠ [])

lemma point_wordAction : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorPoint.point W τ h = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorPoint.point W (τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f) hf := by
  let i := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h
  have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.column_wordAction_nonempty W f (τ.obj 0) i (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W τ h)
  calc
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorPoint.point W τ h = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pointAt W (τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f) (f.orderHom i) hi
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.imagePrefix_arrow_mem W f τ h hi) := by
      apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTargetTransport.point_ext W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.generator_eq W f τ h hi).symm
      · exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.marked_prefix_colimit_image W f τ h hi
      · exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residual_colimit_image W f τ h hi
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorPoint.point W (τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f) hf :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pointAt_eq W _ _ hi _ hf (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_wordAction W f (τ.obj 0) h hf).symm

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
