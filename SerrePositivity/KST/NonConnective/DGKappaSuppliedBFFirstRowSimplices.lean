module
public import SerrePositivity.KST.NonConnective.DGKappaSuppliedBFFixedStructure
public import SerrePositivity.KST.NonConnective.DGKappaNativeFibration
public import SerrePositivity.KST.Fibration.RelativeFirstRowSimplexQuotient

/-!
概要：同じ実商の標準単体比較を、元の全四角形同型から実 BF・固定 K 構造射へ渡す。
方針：有限第一行座標を元の正段に戻し、同じ実商核の引き戻しを全関手同型で移す。
規約：全四角形同型・有限図式比較・共終性は明示定理引数。存在や固定 K の Sp 引き戻し性は主張しない。
使われ方：K-6 c4 の正規化全族比較と c5 の Sp 供給を K-7 c5・d3 へ接続する。
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
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.NonConnective
local instance suppliedBFFirstRowSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
  (hIso : FunctorIso ((dgKappaNativeVerdierDiagram R D I).square ≫
    coherentNerveMap (stableMultiKanEnrichedFunctor.{max (u + 1) v} 0))
    (quotientSKernelInfinitySquare (dgKappaNativeKernelInclusion R D I)
      (dgKappaNativeQuotient R D I)))
  (hrow : ∀ n : ℕ, IsIso (AnodyneHomotopy.anodyneQ.map
    (relativeFirstRowSimplexQuotient (dgKappaNativeQuotient R D I) n)))

include hIso hrow in
/-- 概要：指定全四角形同型と標準単体商比較から、同じ未完備全 S• 四角形は引き戻し。
方針：同じ商の正段比較へ戻してから、元の実核四角形の引き戻しを移す。
規約：hIso・hrow に条件付きで、局所化や全族比較の存在は結論しない。
使われ方：K-6 c4・c5 の独立した二供給を同じ D-9 実列へ代入する。 -/
theorem dgKappaNativeFullSSquare_isPullback_of_kernelIso_firstRowSimplices :
    IsPullbackSquare ((dgKappaNativeVerdierDiagram R D I).square ≫
      coherentNerveMap (stableMultiKanEnrichedFunctor.{max (u + 1) v} 0)) :=
  (dgKappaNativeQuotientSKernel_isPullback R D I
    (fun n => (relativeSQuotient_localized_isIso_iff_firstRowSimplex
      (dgKappaNativeQuotient R D I) n).mpr (hrow n))).of_functorIso hIso.symm

include hIso hrow in
/-- 概要：同じ二比較から、実供給 BF 四角形の実 fiber 比較は非負次数 π 同型。
方針：一回の同じ全 S• 引き戻しを元の実 BF fiber 比較へ渡す。
規約：hIso・hrow に条件付き。固定連結 K の Sp 引き戻し性は使わない。
使われ方：K-6 d の連結範囲を同じ実 fiber 上で読む。 -/
theorem dgKappaSuppliedBFFiber_nonnegative_of_kernelIso_firstRowSimplices
    (j : ℤ) (hj : 0 ≤ j) :
    Function.Bijective (SpectrumHo.piMap (Truncated.HomotopyCategory.homMk
      (SSet.Edge.ofTruncated (dgKappaSuppliedBFFiberComparison R D I)).toTruncated) j) :=
  dgKappaSuppliedBFFiberComparison_nonnegative R D I
    (dgKappaNativeFullSSquare_isPullback_of_kernelIso_firstRowSimplices R D I hIso hrow) j hj

include hIso hrow in
/-- 概要：同じ標準単体商比較と全四角形同型から、固定 K 構造射の非負次数 π 同型。
方針：同じ実 BF fiber 比較と cone 零性に、元の完備化の共終性を続ける。
規約：hIso・hrow・hcofinal に条件付き。K₀ 全射性や全段の Sp 引き戻し性は要求しない。
使われ方：K-7 c5・d3 の同じ cone の構造射への受け渡し。 -/
theorem dgKappaSuppliedBFFixedStructure_nonnegative_of_kernelIso_firstRowSimplices
    (hcofinal : ∀ (X Y : StableModel.{max (u + 1) v}) (f : X ⟶ Y),
      F2.Idempotent.IsIdempotentCompletion f.val →
        (∀ j : ℤ, 0 < j → Function.Bijective (OmegaSpectrum.homotopyMap (kSpectrumMap f) j)) ∧
          Function.Injective (OmegaSpectrum.homotopyMap (kSpectrumMap f) 0))
    (Z : DGKappaZeroInput R D I) (j : ℤ) (hj : 0 ≤ j) :
    Function.Bijective (OmegaSpectrum.homotopyMap (dgKappaNativeStructureMap R D I
      (dgKappaSuppliedBFOldFibrationEdge R D I hcofinal Z)) j) :=
  dgKappaSuppliedBFFixedStructureMap_nonnegative R D I hcofinal Z
    (dgKappaNativeFullSSquare_isPullback_of_kernelIso_firstRowSimplices R D I hIso hrow) j hj

end SerrePositivity.KST.NonConnective
