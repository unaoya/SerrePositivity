module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneSpectrumFunctor
public import SerrePositivity.KST.Spectra.SpectrumWhiteheadEquivalence

/-!
# 通常の複体図式から native Sp への実写像は準同型を反転する

DAG XIII §2.2 の降下への前段。全段の π 同型から構成済みの Sp の Whitehead 比較を使う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded
open SerrePositivity.KST.Spectra (OmegaSpectrum)
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open IsomorphismsAndIsofibrations (IsInvertibleEdge isInvertibleEdge_congr)
variable (A : Type u) [CommRing A]
local instance : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory

/-- 全段の準同型の像は、同じ実スペクトルの coherent な辺として可逆。 -/
lemma eilenbergMacLaneSpectrumMap_isInvertible {M N : Complex A} (f : M ⟶ N)
    [QuasiIso f] :
    IsInvertibleEdge (coherentNerveEdge ((eilenbergMacLaneSpectrumFunctor A).map f)) :=
  KST.Spectra.SpectrumMappingAcyclic.isInvertible_of_levelwise _
    (fun n => eilenbergMacLaneSpectrumMap_piIsomorphism A f n)

/-- 同じ通常 nerve 上の実写像は、全ての準同型の辺を native Sp で反転する。 -/
lemma eilenbergMacLaneOrdinaryNative_map_weak {M N : Complex A} (f : M ⟶ N)
    [QuasiIso f] :
    IsInvertibleEdge ((nerve.edgeMk f).map (eilenbergMacLaneOrdinaryNative A)).toTruncated := by
  apply (isInvertibleEdge_congr
    (e := coherentNerveEdge ((eilenbergMacLaneSpectrumFunctor A).map f))
    (f := ((nerve.edgeMk f).map (eilenbergMacLaneOrdinaryNative A)).toTruncated) ?_).mp
      (eilenbergMacLaneSpectrumMap_isInvertible A f)
  change (nerveToCoherent OmegaSpectrum.{u}).app (Opposite.op ⦋1⦌)
    (ComposableArrows.mk₁ ((eilenbergMacLaneSpectrumFunctor A).map f)) =
    (eilenbergMacLaneOrdinaryNative A).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ f)
  simp only [eilenbergMacLaneOrdinaryNative, omegaSequenceNative,
    NatTrans.comp_app_apply, nerveMap_app_mk₁]
  rfl

end SerrePositivity.EInfinity.PowerOperation
