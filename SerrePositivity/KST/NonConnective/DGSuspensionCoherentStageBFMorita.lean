module
public import SerrePositivity.KST.NonConnective.DGSuspensionCoherentStageMorita
public import SerrePositivity.KST.NonConnective.DGNonconnectiveK
public import SerrePositivity.KST.LocalizingInvariants.SpectrumEdgePi

/-!
概要：B1 全作用の同じ K/loop 段の辺を、元の非連結 K 列の BF 射として復号する。
方針：同じ辺成分を保持する正本 edgeMap と整数 π 関手を使う。
規約：この段別復号から厳密逐次自然性や全入力関手性を結論しない。
使われ方：K-7 e の全単体段族と実 BF 比較射の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.DifferentialGraded
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.NonConnective
local instance coherentStageBFMoritaSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) [Fact κ.IsRegular]
  (hκ : Cardinal.aleph0 < κ)
  (a : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSuspensionCoherentActionInput R (dgKappaUnconditionalStageProvider.{u, v} R κ hκ))
  {A B : PerfDGInput.{u, max (u + 1) v} R} (f : A ⟶ B)

/-- 元の同じ BF 逐次列の対象間に、全単体段族の元の辺を保持する復号射。 -/
def dgSuspensionCoherentStageBFMap (n : ℕ) :
    dgNonconnectiveKStage R κ hκ A n ⟶ dgNonconnectiveKStage R κ hκ B n :=
  SpectrumHo.edgeMap (dgSuspensionCoherentStageMappedEdge R
    (dgKappaUnconditionalStageProvider R κ hκ) a f n)

/-- 復号した同じ BF 射の辺成分は、元の全単体段族の像そのもの。 -/
theorem dgSuspensionCoherentStageBFMap_edge (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgSuspensionCoherentStageBFMap R κ hκ a f n)).edge =
      (dgSuspensionCoherentStageFamily R (dgKappaUnconditionalStageProvider R κ hκ) a n).app
        (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge :=
  SpectrumHo.edgeMap_edge _

variable (hd : ∀ {C D : PerfDGInput.{u, max (u + 1) v} R} (g : C ⟶ D),
    a.data g = dgKappaUnconditionalSuspensionMapData R κ hκ g)
  [(quasiEquivalencePerfectExtension R A B f.down).IsEquivalence]
include hd

/-- 元の同じ全単体段族を復号した BF 射は、Morita 射で全整数 π 同型。 -/
theorem dgSuspensionCoherentStageBFMap_piIsomorphism (n : ℕ) :
    OmegaSpectrum.PiIsomorphism (dgSuspensionCoherentStageBFMap R κ hκ a f n) := by
  let e := dgSuspensionCoherentStageMappedEdge R
    (dgKappaUnconditionalStageProvider R κ hκ) a f n
  let : IsIso (Truncated.HomotopyCategory.homMk e.toTruncated) :=
    dgSuspensionCoherentStageMappedEdge_isInvertible_of_morita R κ hκ a hd f n
  intro j
  have hb := ConcreteCategory.bijective_of_isIso
    ((SpectrumHo.piFunctor j).map (Truncated.HomotopyCategory.homMk e.toTruncated))
  change Function.Bijective (SpectrumHo.piMap
    (Truncated.HomotopyCategory.homMk e.toTruncated) j) at hb
  rw [SpectrumHo.piMap_edge] at hb
  exact hb

end SerrePositivity.KST.NonConnective
