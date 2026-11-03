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
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.FiberModel

variable {X Y : OmegaSpectrum.{u}} (p : X ⟶ Y) [hp : ∀ n, Fibration (p.app n).right]

lemma cone_condition : inclusion p hp ≫ p =
    spectrumPoint_isTerminal.from (obj p hp) ≫ fromPoint Y := by
  apply OmegaSpectrum.Hom.ext
  intro n
  exact (pointedFiberι_comp (p.app n)).trans (pointComposite_zero _).symm

/-- 実 fiber と元の包含を頂点・脚とする通常の錐。 -/
def ordinaryCone : PullbackCone p (fromPoint Y) :=
  PullbackCone.mk (inclusion p hp) (spectrumPoint_isTerminal.from (obj p hp)) (cone_condition p)

/-- 普遍性は各段の既存の実 fiber の普遍性そのもの。 -/
def ordinaryCone_level_isLimit (n : ℕ) :
    IsLimit ((spectrumLevelFunctor n).mapCone (ordinaryCone p)) :=
  (isLimitMapConePullbackConeEquiv (spectrumLevelFunctor n) (cone_condition p)).symm
    (pointedCone_isLimit (p.app n))

/-- γ3 が消費する小さい通常図式の錐。 -/
def smallCone : Cone (spectrumPullbackDiagram p (fromPoint Y)) :=
  (ordinaryCone p).whisker (AsSmall.down : AsSmall.{u} WalkingCospan ⥤ WalkingCospan)

def smallCone_level_isLimit (n : ℕ) : IsLimit (spectrumLevelCone (smallCone p) n) :=
  (ordinaryCone_level_isLimit p n).whiskerEquivalence
    (AsSmall.equiv : WalkingCospan ≌ AsSmall.{u} WalkingCospan).symm

local instance rawFiberConeSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance rawFiberConeHomKan (E B : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom E B) := OmegaSpectrum.mappingSpace_kanComplex E B

/-- この錐は元の全ての豊穣 Hom で極限。 -/
def smallCone_hom_isLimit (Z : OmegaSpectrum.{u}) :
    IsLimit (simplicialHomCone (smallCone p) Z) :=
  spectrumHomCone_isLimit_of_levelwise _ (smallCone_level_isLimit p) Z

/-- 構成した実 fiber を頂点に持つ実際の Sp の錐。 -/
def infinityCone : JoinCone (strictCoherentDiagram (spectrumPullbackDiagram p (fromPoint Y))) :=
  strictCoherentCone (smallCone p)

/-- 実 fiber の錐の Sp における極限性。 -/
lemma infinityCone_isLimit : IsLimitCone (infinityCone p) := by
  have : ∀ Z : OmegaSpectrum.{u}, Fibration
      ((simplicialHomDiagram (spectrumPullbackDiagram p (fromPoint Y)) Z).map
        (AsSmall.up.map WalkingCospan.Hom.inl)) := fun Z ↦ by
    change Fibration
      (((SimplicialCategory.sHomFunctor OmegaSpectrum.{u}).obj (Opposite.op Z)).map p)
    exact spectrumHomMap_fibration Z p
  exact strictCoherentCone_isLimit_of_cospan_homLimit (smallCone p) (smallCone_hom_isLimit p)

lemma infinityCone_vertex : (infinityCone p).vertex = coherentNerveVertex (obj p hp) :=
  strictCoherentCone_vertex _

end SerrePositivity.KST.LocalizingInvariants.FiberModel
