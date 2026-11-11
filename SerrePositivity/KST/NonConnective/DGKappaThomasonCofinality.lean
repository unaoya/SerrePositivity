module
public import SerrePositivity.KST.SConstruction.Cofinality.Thomason
public import SerrePositivity.KST.NonConnective.DGKappaRawSuspensionCompletion
public import SerrePositivity.KST.NonConnective.DGKappaConeCofinality

/-!
概要：Thomason の実証明を同じ cone・実商・固定 K の共終性消費側へ代入する。
方針：指定完備化射の正次数全単射と零次単射を、そのまま既存の引数型へ渡す。
規約：共終性の追加仮定・K₀ 全射性・全入力作用は導入しない。
使われ方：K-7 c5・d3・e の同じ実 BF 候補と完備化比較。
-/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective

/-- 元の共終性引数型に対する、K-cof 正本の実証明。 -/
theorem dgKThomasonCofinality (X Y : StableModel.{u}) (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    (∀ j : ℤ, 0 < j → Function.Bijective (OmegaSpectrum.homotopyMap (kSpectrumMap f) j)) ∧
      Function.Injective (OmegaSpectrum.homotopyMap (kSpectrumMap f) 0) :=
  Cofinality.kSpectrumMap_cofinality f hf

variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 同じ実商から固定 K への比較は、追加の共終性入力なしで正次数 π 同型。 -/
theorem dgKappaRawSuspensionToFixedK_positive_thomason (j : ℤ) (hj : 0 < j) :
    Function.Bijective (OmegaSpectrum.homotopyMap (dgKappaRawSuspensionToFixedK R D I) j) :=
  dgKappaRawSuspensionToFixedK_positive R D I dgKThomasonCofinality j hj

/-- 同じ実商から固定 K への比較は零次単射。零次全射性は要求しない。 -/
theorem dgKappaRawSuspensionToFixedK_zero_injective_thomason :
    Function.Injective (OmegaSpectrum.homotopyMap (dgKappaRawSuspensionToFixedK R D I) 0) :=
  dgKappaRawSuspensionToFixedK_zero_injective R D I dgKThomasonCofinality

/-- 同じ cone の完備化前の K 零性に残っていた共終性入力を放電する。 -/
theorem dgKappaConeNativeK_subsingleton_thomason (Z : DGKappaZeroInput R D I) (j : ℤ) :
    Subsingleton (OmegaSpectrum.homotopyGroup
      (kOmegaSpectrum (dgKappaConeYonedaSource R D I)) j) :=
  dgKappaConeNativeK_subsingleton R D I dgKThomasonCofinality Z j

end SerrePositivity.KST.NonConnective
