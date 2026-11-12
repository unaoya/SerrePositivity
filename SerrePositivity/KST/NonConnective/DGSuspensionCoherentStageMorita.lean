module
public import SerrePositivity.KST.NonConnective.DGSuspensionCoherentStageFamily
public import SerrePositivity.KST.NonConnective.DGSuspensionEdgeIsoInvertibility
public import SerrePositivity.KST.NonConnective.DGSuspensionUnconditionalIterationMorita

/-!
概要：新提供者の同じ実 data を持つ B1 全作用の K/loop 各段は Morita 辺を可逆にする。
方針：実反復射の同値性を、元の固定 K・loop と指定された端点固定比較へ渡す。
規約：B1 作用の存在や構造辺の自然性は推論しない。
使われ方：K-7 e の実全入力段族へ、初期 Morita 入力を直接消費する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.DifferentialGraded
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective
local instance coherentStageMoritaSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) [Fact κ.IsRegular]
  (hκ : Cardinal.aleph0 < κ)
  (a : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSuspensionCoherentActionInput R (dgKappaUnconditionalStageProvider.{u, v} R κ hκ))
  (hd : ∀ {A B : PerfDGInput.{u, max (u + 1) v} R} (f : A ⟶ B),
    a.data f = dgKappaUnconditionalSuspensionMapData R κ hκ f)
include hd

/-- 同じ実 data を持つ作用の厳密反復射は、元の無条件反復射そのもの。 -/
theorem dgSuspensionCoherentIterationMap_eq_unconditional
    {A B : PerfDGInput.{u, max (u + 1) v} R} (f : A ⟶ B) (n : ℕ) :
    dgSuspensionIterationMap R (dgKappaUnconditionalStageProvider R κ hκ) a.data f n =
      dgSuspensionUnconditionalIterationMap R κ hκ f n := by
  have ha : (fun {A B : PerfDGInput.{u, max (u + 1) v} R} (g : A ⟶ B) => a.data g) =
      (fun {A B : PerfDGInput.{u, max (u + 1) v} R} (g : A ⟶ B) =>
        dgKappaUnconditionalSuspensionMapData R κ hκ g) := by
    funext A B f
    exact hd f
  exact congrArg (fun act => dgSuspensionIterationMap R
    (dgKappaUnconditionalStageProvider R κ hκ) act f n) ha

variable {A B : PerfDGInput.{u, max (u + 1) v} R} (f : A ⟶ B)
  [(quasiEquivalencePerfectExtension R A B f.down).IsEquivalence]

/-- 同じ実 Morita 射の K/loop 指定辺は全段で可逆。 -/
theorem dgSuspensionCoherentStageInputEdge_isInvertible_of_morita (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (dgSuspensionCoherentStageInputEdge R
      (dgKappaUnconditionalStageProvider R κ hκ) a f n) := by
  unfold dgSuspensionCoherentStageInputEdge
  rw [dgSuspensionCoherentIterationMap_eq_unconditional R κ hκ a hd f n]
  exact (OmegaSpectrum.isInvertible_of_piIsomorphism _
    (dgSuspensionUnconditionalIterationKMap_piIsomorphism R κ hκ f n)).map _

/-- B1 の指定比較を通して、全作用の同じ正規化辺も Morita 射で可逆。 -/
theorem dgSuspensionCoherentStageMappedEdge_isInvertible_of_morita (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (dgSuspensionCoherentStageMappedEdge R
      (dgKappaUnconditionalStageProvider R κ hκ) a f n) :=
  (suspensionEdgeIso_isInvertible_iff (dgSuspensionCoherentStageFamily_edgeIso R
    (dgKappaUnconditionalStageProvider R κ hκ) a f n)).mpr
      (dgSuspensionCoherentStageInputEdge_isInvertible_of_morita R κ hκ a hd f n)

/-- 同じ全単体 K/loop 段族が送る元の Morita 辺自身は可逆。 -/
theorem dgSuspensionCoherentStageFamily_morita_isInvertible (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((dgSuspensionCoherentStageFamily R
      (dgKappaUnconditionalStageProvider R κ hκ) a n).app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := dgSuspensionCoherentStageMappedEdge R
    (dgKappaUnconditionalStageProvider R κ hκ) a f n)
    (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((dgSuspensionCoherentStageFamily R
      (dgKappaUnconditionalStageProvider R κ hκ) a n).app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge)) rfl).mp
      (dgSuspensionCoherentStageMappedEdge_isInvertible_of_morita R κ hκ a hd f n)

end SerrePositivity.KST.NonConnective
