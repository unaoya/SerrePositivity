module

public import SerrePositivity.KST.LocalizingInvariants.RawFiberSpectrum
public import SerrePositivity.KST.LocalizingInvariants.PointedFiberLimit
public import SerrePositivity.KST.Spectra.SpectrumZeroObject
public import SerrePositivity.KST.Spectra.Limits.SpectrumHomFibrations

/-!
概要：実 fiber の各段と包含を保持する Sp の極限錐。
方針：点つき段の極限性を実写像空間に移し、cospan の Hom 判定を適用する。
規約：左脚だけに段ごとの fibration 性を要求する。使われ方：K-5 の長完全列の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.FiberModel

variable {X Y : OmegaSpectrum.{u}} (p : X ⟶ Y) [hp : ∀ n, Fibration (p.app n).right]

lemma cone_condition : inclusion p hp ≫ p =
    _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint_isTerminal.from (obj p hp) ≫ fromPoint Y := by
  apply OmegaSpectrum.Hom.ext
  intro n
  exact (pointedFiberι_comp (p.app n)).trans (pointComposite_zero _).symm

/-- 実 fiber と元の包含を頂点・脚とする通常の錐。 -/
def ordinaryCone : PullbackCone p (fromPoint Y) :=
  PullbackCone.mk (inclusion p hp) (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint_isTerminal.from (obj p hp)) (cone_condition p)

/-- 普遍性は各段の既存の実 fiber の普遍性そのもの。 -/
def ordinaryCone_level_isLimit (n : ℕ) :
    IsLimit ((_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumLevelFunctor n).mapCone (ordinaryCone p)) :=
  (isLimitMapConePullbackConeEquiv (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumLevelFunctor n) (cone_condition p)).symm
    (pointedCone_isLimit (p.app n))

/-- γ3 が消費する小さい通常図式の錐。 -/
def smallCone : Cone (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackDiagram p (fromPoint Y)) :=
  (ordinaryCone p).whisker (AsSmall.down : AsSmall.{u} WalkingCospan ⥤ WalkingCospan)

def smallCone_level_isLimit (n : ℕ) : IsLimit (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumLevelCone (smallCone p) n) :=
  (_root_.SerrePositivity.KST.LocalizingInvariants.FiberModel.ordinaryCone_level_isLimit p n).whiskerEquivalence
    (AsSmall.equiv : WalkingCospan ≌ AsSmall.{u} WalkingCospan).symm

local instance rawFiberConeSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance rawFiberConeHomKan (E B : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom E B) := OmegaSpectrum.mappingSpace_kanComplex E B

/-- この錐は元の全ての豊穣 Hom で極限。 -/
def smallCone_hom_isLimit (Z : OmegaSpectrum.{u}) :
    IsLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone (_root_.SerrePositivity.KST.LocalizingInvariants.FiberModel.smallCone p) Z) :=
  _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumHomCone_isLimit_of_levelwise _ (smallCone_level_isLimit p) Z

/-- 構成した実 fiber を頂点に持つ実際の Sp の錐。 -/
def infinityCone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackDiagram p (fromPoint Y))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone (_root_.SerrePositivity.KST.LocalizingInvariants.FiberModel.smallCone p)

/-- 実 fiber の錐の Sp における極限性。 -/
lemma infinityCone_isLimit : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.KST.LocalizingInvariants.FiberModel.infinityCone p) := by
  have : ∀ Z : OmegaSpectrum.{u}, Fibration
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackDiagram p (fromPoint Y)) Z).map
        (AsSmall.up.map WalkingCospan.Hom.inl)) := fun Z ↦ by
    change Fibration
      (((SimplicialCategory.sHomFunctor OmegaSpectrum.{u}).obj (Opposite.op Z)).map p)
    exact _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumHomMap_fibration Z p
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.strictCoherentCone_isLimit_of_cospan_homLimit (smallCone p) (smallCone_hom_isLimit p)

lemma infinityCone_vertex : (_root_.SerrePositivity.KST.LocalizingInvariants.FiberModel.infinityCone p).vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (obj p hp) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone_vertex _

end SerrePositivity.KST.LocalizingInvariants.FiberModel
