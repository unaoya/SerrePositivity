module
public import SerrePositivity.KST.SConstruction.Cofinality.RelativeFlagStableModel

/-!
概要：元の相対旗から周囲の全旗への包含を完全射として保持する。
方針：供給側 R_P との同じ完全同型と閉じた全部分圏の包含を合成する。
規約：底の射は元の ambient 全旗への包含そのもの。
使われ方：S 構成の相対旗転置の点ごとの gapped 条件。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：元の相対旗の周囲の全旗への完全な包含。
方針：同じ R_P への逆同型と元の閉部分圏包含を合成する。
規約：元の対象と全自然変換を保持する。
使われ方：相対旗の S 構成の評価。 -/
def completionRelativeFlagAmbientMap (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (n : SimplexCategory) :
    completionRelativeFlagStableModel r ι f hf n ⟶
      Fibration.ambientDiagramModel (stdSimplex.obj n)
        (Fibration.Relative.flagAmbient (((multiSEndofunctor r).obj ι).obj Y)) :=
  (completionClosedFlagStableIso r ι f hf n).inv ≫
    closedStableInclusion (Fibration.Relative.closedFlagStablePredicate
      (completionImageClosedPredicate r ι f hf) n)

/-- 概要：完全な相対旗包含の底は元の周囲の関手圏への包含。
方針：元の全部分圏の二つの持ち上げを計算する。
規約：同型による同一視ではなく射の等号。
使われ方：元の相対 S 図式の包含の回収。 -/
lemma completionRelativeFlagAmbientMap_val (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (n : SimplexCategory) :
    (completionRelativeFlagAmbientMap r ι f hf n).val =
      multiRelativeFlagsInclusion r ι Y
        (multiWideStageData stableWideCofinalitySupply r ι f hf).subcomplex
        (stdSimplex.obj n) := rfl

end SerrePositivity.KST.SConstruction.Cofinality
