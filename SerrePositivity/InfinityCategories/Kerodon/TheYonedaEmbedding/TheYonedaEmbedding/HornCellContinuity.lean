module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.HornCellStep
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.FilteredColimitFunctorClosure

/-!
概要：全ホーンを付加する具体的な一段の関手は filtered 余極限を保つ。
方針：有限ホーンのコピー関手の保存性を、全次元の余積と pushout へ移す。
規約：既存の任意に選ばれた Kan 置換に保存性を仮定しない。
使われ方：連続な Kan 置換を反復の余極限で構成するための一段の保存性。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

/-- 概要：全ホーンの始域のコピーの余積関手は filtered 余極限を保つ。
方針：有限ホーンごとのコピー関手の保存性を余積で保つ。
規約：全ての次元と除外頂点を含む。使われ方：セル付加の始域の連続性。 -/
instance hornSourceCopies_preservesFilteredColimits :
    PreservesFilteredColimitsOfSize.{u, u} _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.hornSourceCopies.{u} := by
  let D := Discrete.functor (fun h : Σ n : ℕ, Fin (n + 2) ↦
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.cellCopiesFunctor (horn (h.1 + 1) h.2 : SSet.{u}) (horn (h.1 + 1) h.2))
  have : ∀ h, PreservesFilteredColimitsOfSize.{u, u} (D.obj h) := by
    intro h
    change PreservesFilteredColimitsOfSize.{u, u}
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.cellCopiesFunctor (horn (h.as.1 + 1) h.as.2 : SSet.{u}) (horn (h.as.1 + 1) h.as.2))
    infer_instance
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.preservesFilteredColimits_colimit_of_pointwise D

/-- 概要：全ホーンの終域のコピーの余積関手は filtered 余極限を保つ。
方針：有限ホーンによる添字の保存性と余積の保存性を合成する。
規約：有限なのは射を添字付けるホーン。使われ方：付加セルの連続性。 -/
instance hornTargetCopies_preservesFilteredColimits :
    PreservesFilteredColimitsOfSize.{u, u} _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.hornTargetCopies.{u} := by
  let D := Discrete.functor (fun h : Σ n : ℕ, Fin (n + 2) ↦
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.cellCopiesFunctor (horn (h.1 + 1) h.2 : SSet.{u}) (stdSimplex.obj ⦋h.1 + 1⦌))
  have : ∀ h, PreservesFilteredColimitsOfSize.{u, u} (D.obj h) := by
    intro h
    change PreservesFilteredColimitsOfSize.{u, u}
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.cellCopiesFunctor (horn (h.as.1 + 1) h.as.2 : SSet.{u}) Δ[h.as.1 + 1])
    infer_instance
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.preservesFilteredColimits_colimit_of_pointwise D

/-- 概要：全ホーンの一段のセル付加関手は filtered 余極限を保つ。
方針：評価と境界の span の三つの関手の保存性を pushout に移す。
規約：保存性はこの具体的な関手に対して証明する。
使われ方：Kan 置換の有限部分複体への境界因子分解。 -/
instance hornCellStep_preservesFilteredColimits :
    PreservesFilteredColimitsOfSize.{u, u} _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.hornCellStep.{u} := by
  have : ∀ j, PreservesFilteredColimitsOfSize.{u, u}
      ((span _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.hornCopiesEvaluation.{u} _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.hornCopiesBoundary.{u}).obj j) := by
    intro j
    cases j with
    | none =>
      change PreservesFilteredColimitsOfSize.{u, u} _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.hornSourceCopies.{u}
      infer_instance
    | some k =>
      cases k with
      | left =>
        change PreservesFilteredColimitsOfSize.{u, u} (𝟭 SSet.{u})
        infer_instance
      | right =>
        change PreservesFilteredColimitsOfSize.{u, u} _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.hornTargetCopies.{u}
        infer_instance
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.preservesFilteredColimits_colimit_of_pointwise
    (span _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.hornCopiesEvaluation.{u} _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.hornCopiesBoundary.{u})

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
