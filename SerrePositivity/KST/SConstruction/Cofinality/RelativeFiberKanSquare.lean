module
public import SerrePositivity.KST.SConstruction.Cofinality.ClosedRelativeExInfinityVanishing
public import SerrePositivity.KST.Fibration.Relative.ClosedRealizationPullback
public import SerrePositivity.KST.Comparison.ExInfinityHomotopyPullback
public import SerrePositivity.KST.Comparison.LocalizedHomotopyComparison

/-!
概要：K-B2-S1 の明示入力から元の本質像包含の Kan 四角形の比較を構成する。
方針：供給側の元の四辺を Ex∞ に送り、同じホモトピー引き戻し比較を使う。
規約：未供給の全旗自然性だけを公開型の Prop 引数に保持する。
使われ方：元の K 射へ戻す長完全列の比較。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.SimplicialModel
open SerrePositivity.KST.Comparison
open scoped Simplicial

/-- 概要：元の本質像包含と元の定数旗の Kan 四角形。
方針：K-B2 の同じ元の四角形を Ex∞ へ送る。
規約：包含の実現と定数旗の四辺を置換前から保持する。
使われ方：元の包含の π 群条件の検査。 -/
theorem completionRelativeKanSquare (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    CommSq
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (coreSRealizationFunctor.map
        (closedStableInclusion (completionImageClosedPredicate r ι f hf))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (Fibration.Relative.closedKernelConstant
        (completionImageClosedPredicate r ι f hf)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (Fibration.Relative.closedRelativeConstant
        (completionImageClosedPredicate r ι f hf)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (Fibration.Relative.closedKernelRealizationPost
        (completionImageClosedPredicate r ι f hf))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map_commSq
    (Fibration.Relative.closedRelativeSquare (completionImageClosedPredicate r ι f hf)).flip

/-- 概要：全旗自然性の入力下で元の Kan 四角形はホモトピー引き戻し。
方針：供給側の同じ四角形の結論を Ex∞ で保存する。
規約：商・Verdier 列・主共終性を入力にしない。
使われ方：同じ元の比較の全基点 π 同型。 -/
lemma completionRelativeKanSquare_homotopyPullback_of_input (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (h : Fibration.Relative.ClosedStableFlagPostPullback
      (completionImageClosedPredicate r ι f hf)) :
    IsHomotopyPullback (completionRelativeKanSquare r ι f hf) :=
  (isHomotopyPullback_exInfinity_iff _).mpr
    ((isHomotopyPullback_flip_iff _).mpr
      (Fibration.Relative.closedRelativeSquare_homotopyPullback _ h))

/-- 概要：元の包含の実現から同じ Kan 四角形の実引き戻し模型への比較。
方針：元の同じ四辺のホモトピー引き戻し比較を使う。
規約：全旗自然性の仮定なしでも射は定義される。
使われ方：元の包含の射影回収と π 同型。 -/
def completionRelativeKanComparison (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :=
  homotopyPullbackComparison (completionRelativeKanSquare r ι f hf)

/-- 概要：実比較の第一射影は元の本質像包含の Ex∞ 実現。
方針：元の引き戻し比較の射影公式を使う。
規約：元の包含射を厳密に回収する。
使われ方：長完全列から元の K 射への接続。 -/
lemma completionRelativeKanComparison_projection (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    completionRelativeKanComparison r ι f hf ≫
      pullback.fst _ _ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (coreSRealizationFunctor.map
        (closedStableInclusion (completionImageClosedPredicate r ι f hf))) :=
  homotopyPullbackComparison_fst (completionRelativeKanSquare r ι f hf)

/-- 概要：未供給の全旗自然性を代入すると実比較は全基点 π 同型。
方針：同じ Kan 四角形の局所化可逆性を既存の Kan 比較へ渡す。
規約：元の包含・定数旗・全実現の四角形を保持する。
使われ方：元の K 群比較の左辺の移送。 -/
lemma completionRelativeKanComparison_piIsomorphism_of_input (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (h : Fibration.Relative.ClosedStableFlagPostPullback
      (completionImageClosedPredicate r ι f hf)) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (completionRelativeKanComparison r ι f hf) := by
  let P := completionImageClosedPredicate r ι f hf
  let : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (coreSRealizationFunctor.obj (closedStableModel P))) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_kanComplex _
  let : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj
      (coreSRealizationFunctor.obj (((multiSEndofunctor r).obj ι).obj Y))) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_kanComplex _
  exact kanPiIsomorphism_of_localized_isIso _
    (completionRelativeKanSquare_homotopyPullback_of_input r ι f hf h)

end SerrePositivity.KST.SConstruction.Cofinality
