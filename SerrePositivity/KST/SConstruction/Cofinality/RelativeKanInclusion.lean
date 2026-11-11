module
public import SerrePositivity.KST.SConstruction.Cofinality.RelativeKanProjection

/-!
概要：二つの未供給入力を元の本質像包含の Kan 誘導写像へ接続する。
方針：元の引き戻し比較の π 同型と第一射影の群条件を合成し、元の包含を回収する。
規約：元の指定包含と任意の基点を保持する。
使われ方：元の K 境界空間への比較の出発点。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories

open scoped Simplicial

/-- 概要：元の本質像包含の core S 実現を Ex∞ へ送った射。
方針：元の包含へ二つの既存関手を適用する。
規約：元の群条件へ戻す対象の射そのもの。
使われ方：零次 K 単射・正次数全単射を得る前の次数移動。 -/
def completionRelativeKanInclusion (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (coreSRealizationFunctor.obj
      (closedStableModel (completionImageClosedPredicate r ι f hf))) ⟶
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (coreSRealizationFunctor.obj (((multiSEndofunctor r).obj ι).obj Y)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (coreSRealizationFunctor.map
    (closedStableInclusion (completionImageClosedPredicate r ι f hf)))

/-- 概要：採用済みの二入力下で元の包含は π₁ 単射・二次以上で全単射。
方針：元の比較と第一射影を合成し、その合成が元の包含である等号を使う。
規約：主結論を仮定せず、未供給の一般射影と全旗自然性だけを明示入力にする。
使われ方：元の境界 K 空間の零次・正次数の条件。 -/
lemma completionRelativeKanInclusion_groupConditions_of_inputs
    (supply : KanPullbackCofinalityInput.{u}) (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (h : Fibration.Relative.ClosedStableFlagPostPullback
      (completionImageClosedPredicate r ι f hf))
    (a : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (coreSRealizationFunctor.obj
      (closedStableModel (completionImageClosedPredicate r ι f hf)))) _⦋0⦌) :
    Function.Injective
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map 1 (completionRelativeKanInclusion r ι f hf) (x := a) rfl) ∧
      ∀ n : ℕ, 1 < n → Function.Bijective
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (completionRelativeKanInclusion r ι f hf) (x := a) rfl) := by
  let j := completionRelativeKanComparison r ι f hf
  let q := completionRelativeKanProjection r ι f hf
  have hj : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism
      (j : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (coreSRealizationFunctor.obj
        (closedStableModel (completionImageClosedPredicate r ι f hf))) ⟶
          completionRelativeKanPullback r ι f hf) :=
    completionRelativeKanComparison_piIsomorphism_of_input r ι f hf h
  have hq := completionRelativeKanProjection_groupConditions_of_input supply r ι f hf
    (j.app (Opposite.op ⦋0⦌) a)
  have he : j ≫ q = completionRelativeKanInclusion r ι f hf :=
    completionRelativeKanComparison_projection r ι f hf
  rw [← he]
  have hm (n : ℕ) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (j ≫ q) (x := a) rfl =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n q rfl) ∘ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n j (x := a) rfl) := by
    funext b
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_comp n j rfl q rfl rfl b
  constructor
  · rw [hm 1]
    exact hq.1.comp (hj a 1).1
  · intro n hn
    rw [hm n]
    exact (hq.2 n hn).comp (hj a n)

end SerrePositivity.KST.SConstruction.Cofinality
