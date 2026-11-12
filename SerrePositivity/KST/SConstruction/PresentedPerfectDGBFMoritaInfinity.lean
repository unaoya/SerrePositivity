module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFMorita
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFInfinityFunctor
public import SerrePositivity.KST.Spectra.SpectrumIntegerHomotopyDetection
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.NerveHomEdgeNaturality

/-! # 同じ実 BF Sp 値関手の Morita 辺の可逆性
概要：厳密豊穣 BF 関手の同じ元の Morita 辺の像は Sp で可逆。
方針：元の通常射を一単体で回収し、同じ実 BF 射の整数 π 同型性を使う。
規約：別の辺へ置き換えない。使われ方：K-4d の Sp 値 Morita 不変性。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open SerrePositivity.InfinityCategories SerrePositivity.DifferentialGraded
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 同じ元の BF 単体的圏を値域に使う。 -/
local instance presentedPerfectDGBFMoritaInfinity_simplicialCategory :
    SimplicialCategory OmegaSpectrum.{w} := OmegaSpectrum.simplicialCategory

/-- 同じ Sp 値関手の元の通常 dg 辺の像は、同じ実 BF 射の辺そのもの。 -/
lemma presentedPerfectDGBFInfinityFunctor_edge
    {X Y : PerfDGInput.{u, v} A} (f : X ⟶ Y) :
    (presentedPerfectDGBFInfinityFunctor A).app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (presentedPerfectDGBFMap A f)).edge :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveMap_edge_of_homEquiv (presentedPerfectDGBFEnrichedFunctor A) f
    (presentedPerfectDGBFMap A f) (presentedPerfectDGBFMap_hom A f).symm

/-- 同じ実 BF Morita 射は、Sp の同じ元の辺として可逆。 -/
lemma presentedPerfectDGBFMap_morita_isInvertible
    {X Y : PerfDGInput.{u, v} A} (f : X ⟶ Y)
    [(quasiEquivalencePerfectExtension A X Y f.down).IsEquivalence] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (presentedPerfectDGBFMap A f)) :=
  OmegaSpectrum.isInvertible_of_piIsomorphism _
    (presentedPerfectDGBFMap_morita_piIsomorphism A f)

/-- 元の Morita 辺の同じ Sp 値関手での像は可逆。 -/
lemma presentedPerfectDGBFInfinityFunctor_morita_isInvertible
    {X Y : PerfDGInput.{u, v} A} (f : X ⟶ Y)
    [(quasiEquivalencePerfectExtension A X Y f.down).IsEquivalence] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
      ((presentedPerfectDGBFInfinityFunctor A).app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge)) := by
  rw [presentedPerfectDGBFInfinityFunctor_edge]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (e := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (presentedPerfectDGBFMap A f))
    (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (presentedPerfectDGBFMap A f)).edge) rfl).mp
      (presentedPerfectDGBFMap_morita_isInvertible A f)

end SerrePositivity.KST.SConstruction
