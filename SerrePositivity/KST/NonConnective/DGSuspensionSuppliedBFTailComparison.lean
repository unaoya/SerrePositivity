module
public import SerrePositivity.KST.NonConnective.DGSuspensionSuppliedBFSequence
public import SerrePositivity.KST.NonConnective.SequentialCandidateMapPi

/-!
概要：同じ実 BF 反復列の指定比較を、元の全整数末尾表示と照合する。
方針：実余錐の脚の π 自然性を、元の loop 次数比較の順逆で読む。
規約：共終性・一回の S• fibration と実逐次比較に条件付き。全 native 作用の存在は主張しない。
使われ方：K-7 d3 の段別表示を、供給された入力間の比較へ接続する形式部分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
open SerrePositivity.KST.LocalizingInvariants SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.NonConnective
local instance suppliedBFTailComparisonSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
variable (R : Type u) [CommRing R] {κ : Cardinal.{u}}
  (s : DGSuspensionStageProvider.{u, v} R κ)
  (A B : PerfDGInput.{u, max (u + 1) v} R)
  (hcofinal : ∀ (X Y : StableModel.{max (u + 1) v}) (f : X ⟶ Y),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val →
      (∀ j : ℤ, 0 < j → Function.Bijective (OmegaSpectrum.homotopyMap (kSpectrumMap f) j)) ∧
        Function.Injective (OmegaSpectrum.homotopyMap (kSpectrumMap f) 0))
  (ZA : ∀ n : ℕ, DGKappaZeroInput R (dgSuspensionIteration R s A n)
    (dgSuspensionIterationStage R s A n).cone)
  (ZB : ∀ n : ℕ, DGKappaZeroInput R (dgSuspensionIteration R s B n)
    (dgSuspensionIterationStage R s B n).cone)
  (hSA : ∀ n : ℕ, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare
    ((dgKappaNativeVerdierDiagram R (dgSuspensionIteration R s A n)
      (dgSuspensionIterationStage R s A n).cone).square ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor.{max (u + 1) v} 0)))
  (hSB : ∀ n : ℕ, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare
    ((dgKappaNativeVerdierDiagram R (dgSuspensionIteration R s B n)
      (dgSuspensionIterationStage R s B n).cone).square ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor.{max (u + 1) v} 0)))
  (η : dgSuspensionNativeSequence R s A (dgSuspensionSuppliedBFStructureEdge R s A hcofinal ZA) ⟶
    dgSuspensionNativeSequence R s B (dgSuspensionSuppliedBFStructureEdge R s B hcofinal ZB))

set_option maxRecDepth 4096 in
/-- 概要：元の整数末尾表示と、指定した同じ実逐次比較の候補上の作用は可換。
方針：実注入の π 自然性と同じ実余錐の脚の回収式を使う。
規約：hcofinal・hSA・hSB・η に条件付き。dg 射から η の存在は推論しない。
使われ方：K-7 d3 の全整数群表示と、供給された入力比較との照合。 -/
theorem dgSuspensionSuppliedBFCandidate_tailPiEquiv_naturality
    (j : ℤ) (n : ℕ) (hn : (-j).toNat ≤ n)
    (x : OmegaSpectrum.homotopyGroup
      (dgKInputSpectrum R (dgSuspensionIteration R s A n)) (j + n)) :
    OmegaSpectrum.homotopyMap (sequentialCandidateMap η) j
      (dgSuspensionSuppliedBFCandidate_tailPiEquiv R s A hcofinal ZA hSA j n hn x) =
    dgSuspensionSuppliedBFCandidate_tailPiEquiv R s B hcofinal ZB hSB j n hn
      (dgSuspensionNativeSequenceStage_piEquiv R s B n j
        (OmegaSpectrum.homotopyMap (η.app ⟨n⟩) j
          ((dgSuspensionNativeSequenceStage_piEquiv R s A n j).symm x))) := by
  change OmegaSpectrum.homotopyMap (sequentialCandidateMap η) j
      (OmegaSpectrum.homotopyMap (sequentialCandidateColimitLegHom
        (dgSuspensionNativeSequence R s A
          (dgSuspensionSuppliedBFStructureEdge R s A hcofinal ZA)) ⟨n⟩) j
        ((dgSuspensionNativeSequenceStage_piEquiv R s A n j).symm x)) =
    OmegaSpectrum.homotopyMap (sequentialCandidateColimitLegHom
      (dgSuspensionNativeSequence R s B
        (dgSuspensionSuppliedBFStructureEdge R s B hcofinal ZB)) ⟨n⟩) j
      ((dgSuspensionNativeSequenceStage_piEquiv R s B n j).symm
        (dgSuspensionNativeSequenceStage_piEquiv R s B n j
          (OmegaSpectrum.homotopyMap (η.app ⟨n⟩) j
            ((dgSuspensionNativeSequenceStage_piEquiv R s A n j).symm x))))
  rw [MulEquiv.symm_apply_apply, sequentialCandidateColimitLeg_pi,
    sequentialCandidateColimitLeg_pi]
  exact DFunLike.congr_fun (sequentialCandidateMap_pi_injection η ⟨n⟩ j)
    ((dgSuspensionNativeSequenceStage_piEquiv R s A n j).symm x)

set_option maxRecDepth 4096 in
/-- 概要：同じ候補比較の作用を元の十分後の懸垂群座標で厳密に読み戻す。
方針：同じ末尾同型の自然性を順逆の消去で書き直す。
規約：共終性・二つの一回の S• fibration・実逐次比較に条件付き。
使われ方：K-7 d3 の全整数 π 比較を元の実段の作用へ戻す。 -/
theorem dgSuspensionSuppliedBFCandidate_tailPiEquiv_symm_naturality
    (j : ℤ) (n : ℕ) (hn : (-j).toNat ≤ n)
    (y : OmegaSpectrum.homotopyGroup
      (dgSuspensionSuppliedBFCandidate R s A hcofinal ZA) j) :
    (dgSuspensionSuppliedBFCandidate_tailPiEquiv R s B hcofinal ZB hSB j n hn).symm
      (OmegaSpectrum.homotopyMap (sequentialCandidateMap η) j y) =
    dgSuspensionNativeSequenceStage_piEquiv R s B n j
      (OmegaSpectrum.homotopyMap (η.app ⟨n⟩) j
        ((dgSuspensionNativeSequenceStage_piEquiv R s A n j).symm
          ((dgSuspensionSuppliedBFCandidate_tailPiEquiv R s A hcofinal ZA hSA j n hn).symm y))) := by
  apply (dgSuspensionSuppliedBFCandidate_tailPiEquiv R s B hcofinal ZB hSB j n hn).injective
  rw [MulEquiv.apply_symm_apply]
  have h := dgSuspensionSuppliedBFCandidate_tailPiEquiv_naturality
    R s A B hcofinal ZA ZB hSA hSB η j n hn
    ((dgSuspensionSuppliedBFCandidate_tailPiEquiv R s A hcofinal ZA hSA j n hn).symm y)
  rw [MulEquiv.apply_symm_apply] at h
  exact h

end SerrePositivity.KST.NonConnective
