module
public import SerrePositivity.KST.Fibration.Relative.SingleStageDetection
public import SerrePositivity.KST.NonConnective.DGSuspensionSuppliedBFSequence

/-!
概要：K-B2 の相対 S• 比較界面を、同じ固定 K 構造射と反復列の連結比較へ渡す。
方針：同じ未完備実列の二比較から単回引き戻し性を得て既存の実比較へ代入する。
規約：c4・c5 の二比較と共終性に条件付き。固定連結 K の Sp 引き戻し性は要求しない。
使われ方：K-6 d と K-7 c5・d3 の相対 S• 供給の消費。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
open SerrePositivity.KST.LocalizingInvariants SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.NonConnective
local instance relativeComparisonSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory

/-- 概要：K-B2 の同じ相対二比較から固定 K 構造射の非負次数 π 同型を得る。
方針：相対実現の単回引き戻し性を、既存の実供給 BF 構造射へ代入する。
規約：同じ I・Z・固定 K・実構造辺を保持する。二比較と共終性に条件付き。
使われ方：K-6 d から K-7 c5 の実構造射への接続。 -/
theorem dgKappaRelativeFixedStructureMap_nonnegative
    (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
    {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
    (hcofinal : ∀ (X Y : StableModel.{max (u + 1) v}) (f : X ⟶ Y),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val →
        (∀ j : ℤ, 0 < j → Function.Bijective (OmegaSpectrum.homotopyMap (kSpectrumMap f) j)) ∧
          Function.Injective (OmegaSpectrum.homotopyMap (kSpectrumMap f) 0))
    (Z : DGKappaZeroInput R D I)
    (c : Relative.SingleRelativeComparison (dgKappaNativeVerdierDiagram R D I))
    (j : ℤ) (hj : 0 ≤ j) :
    Function.Bijective (OmegaSpectrum.homotopyMap (dgKappaNativeStructureMap R D I
      (dgKappaSuppliedBFOldFibrationEdge R D I hcofinal Z)) j) :=
  dgKappaSuppliedBFFixedStructureMap_nonnegative R D I hcofinal Z
    (c.isPullback (dgKappaNativeVerdierDiagram R D I)) j hj

variable (R : Type u) [CommRing R] {κ : Cardinal.{u}}
  (s : DGSuspensionStageProvider.{u, v} R κ) (A : PerfDGInput.{u, max (u + 1) v} R)
  (hcofinal : ∀ (X Y : StableModel.{max (u + 1) v}) (f : X ⟶ Y),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val →
      (∀ j : ℤ, 0 < j → Function.Bijective (OmegaSpectrum.homotopyMap (kSpectrumMap f) j)) ∧
        Function.Injective (OmegaSpectrum.homotopyMap (kSpectrumMap f) 0))
  (Z : ∀ n : ℕ, DGKappaZeroInput R (dgSuspensionIteration R s A n)
    (dgSuspensionIterationStage R s A n).cone)
  (c : ∀ n : ℕ, Relative.SingleRelativeComparison
    (dgKappaNativeVerdierDiagram R (dgSuspensionIteration R s A n)
      (dgSuspensionIterationStage R s A n).cone))

include c

/-- 概要：段ごとの K-B2 の二比較から同じ実反復列の連結比較の非負次数 π 同型を得る。
方針：各段の単回相対実現を既存の隣接安定化と実余錐へ渡す。
規約：段ごとの二比較・同じ cone・共終性に条件付き。全入力自然性は主張しない。
使われ方：K-7 d3 の元の固定 K から実候補への比較。 -/
theorem dgSuspensionRelativeConnectedComparison_nonnegative (j : ℤ) (hj : 0 ≤ j) :
    Function.Bijective (OmegaSpectrum.homotopyMap
      (dgSuspensionSuppliedBFConnectedComparison R s A hcofinal Z) j) :=
  dgSuspensionSuppliedBFConnectedComparison_nonnegative R s A hcofinal Z
    (fun n => (c n).isPullback _) j hj

/-- 概要：同じ段別二比較は元の SOA 連結 K の比較にも非負次数 π 同型を与える。
方針：既存の実供給列と元の SOA 比較へ同じ単回引き戻し入力を渡す。
規約：元の構造辺・実候補・固定 K の始点を保持する。二比較等に条件付き。
使われ方：K-7 d3 の元の連結 K との比較への代入。 -/
theorem dgSuspensionRelativeSOAComparison_nonnegative (j : ℤ) (hj : 0 ≤ j) :
    Function.Bijective (OmegaSpectrum.homotopyMap
      (dgSuspensionSuppliedBFSOAComparison R s A hcofinal Z) j) :=
  dgSuspensionSuppliedBFSOAComparison_nonnegative R s A hcofinal Z
    (fun n => (c n).isPullback _) j hj

end SerrePositivity.KST.NonConnective
