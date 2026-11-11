module
public import SerrePositivity.KST.NonConnective.DGSuspensionThomasonSequence
public import SerrePositivity.KST.NonConnective.SequentialCandidateMapThomason

/-!
概要：同じ実 BF 候補間の逐次完備化比較を Thomason 共終性で判定する。
方針：元の native loop 座標と同じ SOA 比較の逆を、実 K 射の座標へ合成する。
規約：実逐次比較と元の完備化 K 射との可換性は明示入力。D の未供給作用は推論しない。
使われ方：K-7 e の同じ候補比較の全整数 π 同型・実 Sp 辺の可逆性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.NonConnective
local instance thomasonComparisonSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) [Fact κ.IsRegular]
  (hκ : Cardinal.aleph0 < κ) (A : PerfDGInput.{u, max (u + 1) v} R)

/-- 同じ実反復列を共終性の実証明で固定する。 -/
def dgSuspensionThomasonSequence : SpectrumSequence.{max (u + 1) v} :=
  dgSuspensionNativeSequence R (dgKappaUnconditionalStageProvider.{u, v} R κ hκ) A
    (dgSuspensionThomasonStructureEdge R κ hκ A)

/-- 元の同じ懸垂の ν 値を、SOA K の安定模型として保持する。 -/
def dgSuspensionThomasonSOAModel (n : ℕ) : StableModel.{max (u + 1) v} :=
  stableCategoryModel (presentedPerfectDGStableCategory R
    (dgSuspensionUnconditionalIteration R κ hκ A n))

/-- 同じ実段の native loop 座標を、同じ実 SOA 比較の逆で元の K 群へ戻す。 -/
def dgSuspensionThomasonStageSOACoordinates (n : ℕ) (j : ℤ) :
    OmegaSpectrum.homotopyGroup ((dgSuspensionThomasonSequence R κ hκ A).obj ⟨n⟩) j ≃*
      OmegaSpectrum.homotopyGroup (kOmegaSpectrum
        (dgSuspensionThomasonSOAModel R κ hκ A n)) (j + n) :=
  (dgSuspensionNativeSequenceStage_piEquiv R
    (dgKappaUnconditionalStageProvider.{u, v} R κ hκ) A n j).trans
      (MulEquiv.ofBijective (OmegaSpectrum.homotopyMap
        (presentedPerfectDGBFSOASpectrumComparison R
          (dgSuspensionUnconditionalIteration R κ hκ A n)) (j + n))
        (presentedPerfectDGBFSOASpectrumComparison_piIsomorphism R
          (dgSuspensionUnconditionalIteration R κ hκ A n) (j + n))).symm

variable (B : PerfDGInput.{u, max (u + 1) v} R)
  (η : dgSuspensionThomasonSequence R κ hκ A ⟶ dgSuspensionThomasonSequence R κ hκ B)

/-- 元の実逐次比較から、同じ二つの実非連結化候補間の比較を作る。 -/
def dgSuspensionThomasonCandidateMap :
    dgSuspensionThomasonCandidate R κ hκ A ⟶ dgSuspensionThomasonCandidate R κ hκ B :=
  sequentialCandidateMap η

variable (f : ∀ n, dgSuspensionThomasonSOAModel R κ hκ A n ⟶
    dgSuspensionThomasonSOAModel R κ hκ B n)
  (hf : ∀ n, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion (f n).val)
  (h : ∀ (n : ℕ) (j : ℤ)
    (x : OmegaSpectrum.homotopyGroup ((dgSuspensionThomasonSequence R κ hκ A).obj ⟨n⟩) j),
    dgSuspensionThomasonStageSOACoordinates R κ hκ B n j
        (OmegaSpectrum.homotopyMap (η.app ⟨n⟩) j x) =
      OmegaSpectrum.homotopyMap (kSpectrumMap (f n)) (j + n)
        (dgSuspensionThomasonStageSOACoordinates R κ hκ A n j x))
include hf h

/-- 概要：元の段別完備化 K 射と可換な同じ候補比較は全整数 π 同型。
方針：実 native loop・SOA 座標を工程 e の Thomason 末尾判定へ代入する。
規約：η・f・hf・h は明示入力。共終性・段別 π 全単射性の追加仮定は取らない。
使われ方：同じ実非連結化候補上で完備化比較の不変性を得る。 -/
theorem dgSuspensionThomasonCandidateMap_piIsomorphism_of_completion :
    OmegaSpectrum.PiIsomorphism (dgSuspensionThomasonCandidateMap R κ hκ A B η) :=
  sequentialCandidateMap_piIsomorphism_of_thomason η
    (dgSuspensionThomasonSOAModel R κ hκ A) (dgSuspensionThomasonSOAModel R κ hκ B)
    f hf (dgSuspensionThomasonStageSOACoordinates R κ hκ A)
    (dgSuspensionThomasonStageSOACoordinates R κ hκ B) h

/-- 同じ候補比較の元の実 Sp 辺は可逆。全入力自然性の完成とは数えない。 -/
theorem dgSuspensionThomasonCandidateMap_isInvertible_of_completion :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgSuspensionThomasonCandidateMap R κ hκ A B η)) :=
  OmegaSpectrum.isInvertible_of_piIsomorphism _
    (dgSuspensionThomasonCandidateMap_piIsomorphism_of_completion R κ hκ A B η f hf h)

end SerrePositivity.KST.NonConnective
