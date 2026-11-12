module
public import SerrePositivity.KST.Fibration.DGKZeroComparison
public import SerrePositivity.KST.Fibration.DGKPiComparison

/-! # ν 像が Verdier 列となる同じ dg 商辺の、固定 K の実 π₀ 射の全射性 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.Spectra
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable (A : Type u) [CommRing A] {P Q : PerfDGInput.{u, v} A}

/-- 同じ実 BF 射の零次群の全射性は、元の ν 辺の三角圏 K₀ 作用の全射性と同値。 -/
theorem dgKZeroBFMap_surjective_iff (f : P ⟶ Q) :
    Function.Surjective (OmegaSpectrum.homotopyMap (dgKInputSpectrumMap A f) 0) ↔
      Function.Surjective (dgNuKZeroMap A f) := by
  constructor
  · intro hs a
    obtain ⟨z, hz⟩ := hs (dgKZeroBFEquiv A Q a)
    obtain ⟨b, hb⟩ := (dgKZeroBFEquiv A P).surjective z
    refine ⟨b, (dgKZeroBFEquiv A Q).injective ?_⟩
    exact (dgKZeroBFEquiv_naturality A f b).trans
      ((congrArg (OmegaSpectrum.homotopyMap (dgKInputSpectrumMap A f) 0) hb).trans hz)
  · intro hs z
    obtain ⟨a, ha⟩ := (dgKZeroBFEquiv A Q).surjective z
    obtain ⟨b, hb⟩ := hs a
    refine ⟨dgKZeroBFEquiv A P b, ?_⟩
    exact (dgKZeroBFEquiv_naturality A f b).symm.trans
      ((congrArg (dgKZeroBFEquiv A Q) hb).trans ha)

/-- 固定 K の同じ実辺の零次 π 作用の全射性を、元の ν 辺の K₀ 作用で判定する。 -/
theorem dgKPiZeroMap_surjective_iff_kZero (f : P ⟶ Q) :
    Function.Surjective ((SpectrumHo.piFunctor 0).map
      (Truncated.HomotopyCategory.homMk
        (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).map (dgKInputK A)).toTruncated))).hom ↔
      Function.Surjective (dgNuKZeroMap A f) :=
  (dgKPiMap_surjective_iff A f 0).trans (dgKZeroBFMap_surjective_iff A f)

/-- ν 像が元の Verdier 列なら、同じ固定 K の商辺の実 π₀ 射は全射。局所化性は仮定しない。 -/
theorem dgKPiZeroMap_surjective_of_verdier
    {P Q R : PerfDGInput.{u, v} A} (f : P ⟶ Q) (g : Q ⟶ R)
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence
      (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (dgKInputStableValue A P) (dgKInputStableValue A Q) from dgKInputNuMap A f)
      (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (dgKInputStableValue A Q) (dgKInputStableValue A R) from dgKInputNuMap A g)) :
    Function.Surjective ((SpectrumHo.piFunctor 0).map
      (Truncated.HomotopyCategory.homMk
        (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g).map (dgKInputK A)).toTruncated))).hom :=
  (dgKPiZeroMap_surjective_iff_kZero A g).mpr (dgNuKZeroMap_surjective_of_verdier A f g h)

end SerrePositivity.KST.Fibration
