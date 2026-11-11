module
public import SerrePositivity.KST.SConstruction.Cofinality.CompletionImageEquivalence
public import SerrePositivity.KST.SConstruction.KSpectrumInvariance
public import SerrePositivity.KST.SConstruction.KHomotopyFunctor

/-!
概要：本質像の包含についての群条件を元の指定 K 射の同じ群条件へ戻す。
方針：元の射の厳密な因子化と、始域から本質像への実 K 同値を使う。
規約：スペクトルの射の厳密な合成則を仮定せず、証明済みの整数群の合成則を使う。
使われ方：K-B2-S1 の左項を消去し、元の kSpectrumMap へ結論を移す。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory Spectra
open SerrePositivity.InfinityCategories

set_option maxHeartbeats 800000 in
-- 閉じた本質像の模型と BF 群の依存型を照合するため、局所的に上限を増やす。
/-- 概要：本質像の包含の全単射性は元の同じ反復 S 射の全単射性に等しい。
方針：始域から本質像への全整数 π 同型を合成から消去する。
規約：整数群へ誘導される元の実 K 射を使う。
使われ方：fiber 比較から得た正次数の結論の輸送。 -/
theorem completionK_bijective_iff_imageInclusion (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (j : ℤ) :
    Function.Bijective (OmegaSpectrum.homotopyMap
      (kSpectrumMap (((multiSEndofunctor r).obj ι).map f)) j) ↔
      Function.Bijective (OmegaSpectrum.homotopyMap
        (kSpectrumMap (closedStableInclusion (completionImageClosedPredicate r ι f hf))) j) := by
  let e := completionSourceImageStableEquivalence r ι f hf
  let i := closedStableInclusion (completionImageClosedPredicate r ι f hf)
  have hb := kSpectrumMap_piIsomorphism_of_equivalence e j
  have he : kHomotopyMap (((multiSEndofunctor r).obj ι).map f) j =
      (kHomotopyMap i j).comp (kHomotopyMap e.hom j) :=
    (congrArg (fun q => kHomotopyMap q j)
      (completionSourceImageStableMap_inclusion r ι f hf).symm).trans
        (kHomotopyMap_comp e.hom i j)
  exact (Iff.of_eq (congrArg (fun h : _ →* _ => Function.Bijective h) he)).trans
    (Function.Bijective.of_comp_iff _ hb)

set_option maxHeartbeats 800000 in
-- 閉じた本質像の模型と BF 群の依存型を照合するため、局所的に上限を増やす。
/-- 概要：本質像の包含の単射性も元の同じ反復 S 射の単射性に等しい。
方針：元の始域から本質像への全単射を群の合成から消去する。
規約：零次の全射性を追加しない。
使われ方：fiber 比較から得た零次単射性の輸送。 -/
theorem completionK_injective_iff_imageInclusion (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (j : ℤ) :
    Function.Injective (OmegaSpectrum.homotopyMap
      (kSpectrumMap (((multiSEndofunctor r).obj ι).map f)) j) ↔
      Function.Injective (OmegaSpectrum.homotopyMap
        (kSpectrumMap (closedStableInclusion (completionImageClosedPredicate r ι f hf))) j) := by
  let e := completionSourceImageStableEquivalence r ι f hf
  let i := closedStableInclusion (completionImageClosedPredicate r ι f hf)
  have hb := kSpectrumMap_piIsomorphism_of_equivalence e j
  have he : kHomotopyMap (((multiSEndofunctor r).obj ι).map f) j =
      (kHomotopyMap i j).comp (kHomotopyMap e.hom j) :=
    (congrArg (fun q => kHomotopyMap q j)
      (completionSourceImageStableMap_inclusion r ι f hf).symm).trans
        (kHomotopyMap_comp e.hom i j)
  exact (Iff.of_eq (congrArg (fun h : _ →* _ => Function.Injective h) he)).trans
    (Function.Injective.of_comp_iff' _ hb)

end SerrePositivity.KST.SConstruction.Cofinality
