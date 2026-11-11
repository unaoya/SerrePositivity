module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.FiniteCellCopies
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
概要：filtered 余極限を保つ単体集合の関手の余極限も filtered 余極限を保つ。
方針：図式を反転して各評価で保存性を確認し、余極限関手の左随伴性を使う。
規約：余極限を取る添字と、保存する filtered な添字を区別する。
使われ方：全ホーンのコピーの余積と pushout によるセル付加関手の連続性。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

/-- 概要：filtered 余極限を保つ関手の図式の余極限は filtered 余極限を保つ。
方針：評価ごとの保存性を束ね、関手圏の点ごとの余極限表示へ移す。
規約：保存する図式の宇宙は単体集合と同じ u。
使われ方：余積・pushout・可算反復の余極限で連続性を保つ。 -/
lemma preservesFilteredColimits_colimit_of_pointwise
    {I : Type v} [SmallCategory I] [HasColimitsOfShape I SSet.{u}]
    (D : I ⥤ SSet.{u} ⥤ SSet.{u})
    [∀ i, PreservesFilteredColimitsOfSize.{u, u} (D.obj i)] :
    PreservesFilteredColimitsOfSize.{u, u} (colimit D) where
  preserves_filtered_colimits J _ _ := by
    have : PreservesColimitsOfShape J D.flip :=
      preservesColimitsOfShape_of_evaluation D.flip J (fun i ↦ by
        change PreservesColimitsOfShape J (D.obj i)
        infer_instance)
    have : PreservesColimitsOfShape J (D.flip ⋙ colim) := inferInstance
    exact preservesColimitsOfShape_of_natIso (colimitFlipIsoCompColim D.flip).symm

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
