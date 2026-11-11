module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFMoritaInfinity
public import SerrePositivity.KST.SConstruction.DGKQuasiEquivalence

/-! # 同じ厳密 dg 準同値に対する新 BF K の不変性
概要：元の dg 準同値は、同じ新 BF 射の全段・全整数 π 同型と Sp 辺の可逆性を与える。
方針：元の主 Perf 同値の証明を使い、既証の同じ Morita 射の判定を適用する。
規約：準同値と Morita の条件を区別する。使われ方：K-4d の準同値不変性。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] {X Y : PerfDGInput.{u, v} A} (f : X ⟶ Y)
  (hf : QuasiEquivalence f.down)
include hf

/-- 元の厳密 dg 準同値による同じ新 BF 射は全段で全基点 π 同型。 -/
lemma presentedPerfectDGBFMap_levelwise_of_quasiEquivalence (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((presentedPerfectDGBFMap A f).app n).right := by
  let : (quasiEquivalencePerfectExtension A X Y f.down).IsEquivalence :=
    (quasiEquivalencePerfectEquivalence A X Y f.down hf).isEquivalence_functor
  exact presentedPerfectDGBFMap_morita_levelwise A f n

/-- 元の厳密 dg 準同値による同じ新 BF 射は全整数次数で π 同型。 -/
lemma presentedPerfectDGBFMap_piIsomorphism_of_quasiEquivalence :
    OmegaSpectrum.PiIsomorphism (presentedPerfectDGBFMap A f) :=
  OmegaSpectrum.piIsomorphism_of_levelwise _
    (presentedPerfectDGBFMap_levelwise_of_quasiEquivalence A f hf)

/-- 元の dg 準同値の同じ Sp 値 ∞ 関手での像は可逆。 -/
lemma presentedPerfectDGBFInfinityFunctor_quasiEquivalence_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
      ((presentedPerfectDGBFInfinityFunctor A).app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge)) := by
  let : (quasiEquivalencePerfectExtension A X Y f.down).IsEquivalence :=
    (quasiEquivalencePerfectEquivalence A X Y f.down hf).isEquivalence_functor
  exact presentedPerfectDGBFInfinityFunctor_morita_isInvertible A f

end SerrePositivity.KST.SConstruction
