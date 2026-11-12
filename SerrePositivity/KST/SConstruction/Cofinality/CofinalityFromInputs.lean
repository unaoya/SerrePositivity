module
public import SerrePositivity.KST.SConstruction.Cofinality.BoundaryKTransfer
public import SerrePositivity.KST.SConstruction.Cofinality.ImageInclusionKComparison

/-!
概要：採用済みの二つの供給入力下で元の指定完備化射の実 K 共終性を結論する。
方針：元の本質像包含の Kan 条件を境界 K 射へ移し、始域から本質像への同値を消去する。
規約：元の指定射の kSpectrumMap を結論し、未供給入力を明示する。
使われ方：一般供給の到着後の実証明の代入。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet Spectra
open SerrePositivity.InfinityCategories

open scoped Simplicial

/-- 概要：採用済み一般射影と相対全旗自然性の入力から同じ実 K 射の共終性条件を得る。
方針：元の包含の全基点条件を元の K 射へ移し、本質像との実同値を消去する。
規約：一般共終性を仮定せず、未供給入力だけを明示する。
使われ方：二供給の到着後の無条件な主結論の公開。 -/
theorem kSpectrumMap_cofinality_of_inputs (supply : KanPullbackCofinalityInput.{u})
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (h : Fibration.Relative.ClosedStableFlagPostPullback
      (completionImageClosedPredicate 0 Fin.elim0 f hf)) :
    (∀ j : ℤ, 0 < j → Function.Bijective (OmegaSpectrum.homotopyMap (kSpectrumMap f) j)) ∧
      Function.Injective (OmegaSpectrum.homotopyMap (kSpectrumMap f) 0) := by
  let P := completionImageClosedPredicate 0 Fin.elim0 f hf
  let i := closedStableInclusion P
  have hi := kSpectrumMap_cofinality_of_coreS i
    (completionRelativeKanInclusion_groupConditions_of_inputs supply 0 Fin.elim0 f hf h)
  constructor
  · intro j hj
    exact (completionK_bijective_iff_imageInclusion 0 Fin.elim0 f hf j).mpr (hi.1 j hj)
  · exact (completionK_injective_iff_imageInclusion 0 Fin.elim0 f hf 0).mpr hi.2

end SerrePositivity.KST.SConstruction.Cofinality
