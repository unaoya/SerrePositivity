module

public import SerrePositivity.KST.Spectra.D3CommonRefinement
public import SerrePositivity.KST.Spectra.D3SpectrumCorner
public import SerrePositivity.KST.Spectra.AdjointLoopRelativeFullCoherentComparison

/-!
概要：元の全 Hom と共通比較射を同時に保持する Hom の実解像。
方針：元の FullCompatible Hom の指定二境界に二段左因子の corner を引き戻す。
規約：元の包含と右射影を捨てない。実 loop 図式の全関手比較は後続工程。
使われ方：d3b② の比較射の全 Hom RLP と厳密豊穣合成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance commonHomSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
attribute [local irreducible] commonRefinement

/-- 元の全 Hom が指定する、共通対象の包含・比較の二境界。 -/
def commonBoundaryMap (X Y : OmegaSpectrum.{u}) : fullCompatibleSpace X Y ⟶
    spectrumCornerTarget (commonInclusion X) (commonComparison Y) :=
  pullback.lift
    (fullOriginalMap X Y ≫ eHomWhiskerLeft SSet X (commonInclusion Y))
    (fullReplacedMap X Y ≫ eHomWhiskerRight SSet (commonComparison X) (middle Y)) (by
      rw [Category.assoc, ← eHomWhiskerLeft_comp, commonInclusion_comparison,
        Category.assoc, ← eHomWhiskerRight_comp, commonInclusion_comparison]
      exact (full_left_whiskered X Y).symm)

/-- 指定左境界は元の X,Y の全 Hom と二段包含を回収する。 -/
@[reassoc (attr := simp)]
lemma commonBoundaryMap_fst (X Y : OmegaSpectrum.{u}) :
    commonBoundaryMap X Y ≫ pullback.fst _ _ =
      fullOriginalMap X Y ≫ eHomWhiskerLeft SSet X (commonInclusion Y) :=
  pullback.lift_fst _ _ _

/-- 指定右境界は元の M_X,M_Y の全 Hom と比較右脚を回収する。 -/
@[reassoc (attr := simp)]
lemma commonBoundaryMap_snd (X Y : OmegaSpectrum.{u}) :
    commonBoundaryMap X Y ≫ pullback.snd _ _ =
      fullReplacedMap X Y ≫ eHomWhiskerRight SSet (commonComparison X) (middle Y) :=
  pullback.lift_snd _ _ _

/-- 同じ実引き戻しの存在を SSet の全極限から明示する。 -/
instance commonHom_hasPullback (X Y : OmegaSpectrum.{u}) :
    HasPullback (C := SSet.{u})
      (spectrumCorner (commonInclusion X) (commonComparison Y))
      (commonBoundaryMap X Y) :=
  HasLimitsOfShape.has_limit (J := WalkingCospan) (C := SSet.{u}) _

/-- 比較射と元の全左右因子を同時に保つ Hom の実空間。 -/
def commonHom (X Y : OmegaSpectrum.{u}) : SSet.{u} :=
  pullback (C := SSet.{u})
    (spectrumCorner (commonInclusion X) (commonComparison Y))
    (commonBoundaryMap X Y)

/-- 同じ比較 Hom から共通対象間の元の BF Hom を回収する。 -/
def commonRefinedMap (X Y : OmegaSpectrum.{u}) :
    commonHom X Y ⟶ mappingSpace (commonRefinement X) (commonRefinement Y) := by
  dsimp only [commonHom]
  exact pullback.fst _ _

/-- 元の FullCompatible Hom を同じ全単体で回収する。 -/
def commonBaseMap (X Y : OmegaSpectrum.{u}) : commonHom X Y ⟶ fullCompatibleSpace X Y := by
  dsimp only [commonHom]
  exact pullback.snd _ _

/-- 共通対象の指定二境界の corner を元の BF 豊穣表記で認証する。 -/
lemma commonSpectrumCorner_trivialKanFibration (X Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (spectrumCorner (commonInclusion X) (commonComparison Y)) :=
  spectrumCompositeCorner_trivialKanFibration
    (loopSourceInclusion X) (commonLoopInclusion X) (loopSourceInclusion_relative X)
    (commonLoopInclusion_relative X) (commonComparison Y) (commonComparison_rlp Y)

/-- 共通比較を含む Hom の射影の全単射 RLP を実 corner から証明する。 -/
instance commonBaseMap_trivialKanFibration (X Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (commonBaseMap X Y) := by
  dsimp only [commonBaseMap, commonHom]
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.pullback_snd _ _ (commonSpectrumCorner_trivialKanFibration X Y).mem⟩

/-- 同じ比較 Hom から元の X,Y の Hom を回収する。 -/
def commonOriginalMap (X Y : OmegaSpectrum.{u}) : commonHom X Y ⟶ mappingSpace X Y :=
  commonBaseMap X Y ≫ fullOriginalMap X Y

/-- 同じ比較 Hom から元の相対 BF 対象間の Hom を回収する。 -/
def commonMiddleMap (X Y : OmegaSpectrum.{u}) :
    commonHom X Y ⟶ mappingSpace (middle X) (middle Y) :=
  commonBaseMap X Y ≫ fullReplacedMap X Y

/-- 元の全 Hom への合成射影も、比較を含めて実自明 Kan fibration。 -/
instance commonOriginalMap_trivialKanFibration (X Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (commonOriginalMap X Y) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.comp_mem _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := commonBaseMap X Y))
    (fullOriginalMap_trivialKanFibration X Y).mem⟩

/-- 比較 Hom の左境界は、元の二段包含の全 Hom 正方形。 -/
@[reassoc]
lemma common_left_whiskered (X Y : OmegaSpectrum.{u}) :
    commonRefinedMap X Y ≫ eHomWhiskerRight SSet (commonInclusion X) (commonRefinement Y) =
      commonOriginalMap X Y ≫ eHomWhiskerLeft SSet X (commonInclusion Y) := by
  dsimp only [commonRefinedMap, commonOriginalMap, commonBaseMap, commonHom, id]
  simp only [Category.assoc]
  rw [spectrumCorner_pullback_fst, commonBoundaryMap_fst]

/-- 同じ Hom の右境界は、指定比較射を保つ全 Hom 正方形。 -/
@[reassoc]
lemma common_right_whiskered (X Y : OmegaSpectrum.{u}) :
    commonRefinedMap X Y ≫ eHomWhiskerLeft SSet (commonRefinement X) (commonComparison Y) =
      commonMiddleMap X Y ≫ eHomWhiskerRight SSet (commonComparison X) (middle Y) := by
  dsimp only [commonRefinedMap, commonMiddleMap, commonBaseMap, commonHom, id]
  simp only [Category.assoc]
  rw [spectrumCorner_pullback_snd, commonBoundaryMap_snd]

/-- 二つの実境界を保つ任意の族を、同じ比較 Hom へ束ねる。 -/
def commonHomLift (X Y : OmegaSpectrum.{u}) {U : SSet.{u}}
    (g : U ⟶ mappingSpace (commonRefinement X) (commonRefinement Y))
    (f : U ⟶ fullCompatibleSpace X Y)
    (hl : g ≫ eHomWhiskerRight SSet (commonInclusion X) (commonRefinement Y) =
      f ≫ fullOriginalMap X Y ≫ eHomWhiskerLeft SSet X (commonInclusion Y))
    (hr : g ≫ eHomWhiskerLeft SSet (commonRefinement X) (commonComparison Y) =
      f ≫ fullReplacedMap X Y ≫ eHomWhiskerRight SSet (commonComparison X) (middle Y)) :
    U ⟶ commonHom X Y := by
  dsimp only [commonHom]
  exact pullback.lift g f (by
    apply pullback.hom_ext
    · simpa only [Category.assoc, spectrumCorner_fst,
        commonBoundaryMap_fst] using hl
    · simpa only [Category.assoc, spectrumCorner_snd,
        commonBoundaryMap_snd] using hr)

@[reassoc (attr := simp)]
lemma commonHomLift_refined (X Y : OmegaSpectrum.{u}) {U : SSet.{u}} (g f hl hr) :
    commonHomLift X Y (U := U) g f hl hr ≫ commonRefinedMap X Y = g := by
  dsimp only [commonHomLift, commonRefinedMap]
  exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma commonHomLift_base (X Y : OmegaSpectrum.{u}) {U : SSet.{u}} (g f hl hr) :
    commonHomLift X Y (U := U) g f hl hr ≫ commonBaseMap X Y = f := by
  dsimp only [commonHomLift, commonBaseMap]
  exact pullback.lift_snd _ _ _

/-- 二つの元の射影で全比較 Hom への族を検出する。 -/
lemma commonHom_ext (X Y : OmegaSpectrum.{u}) {U : SSet.{u}} {f g : U ⟶ commonHom X Y}
    (h₁ : f ≫ commonRefinedMap X Y = g ≫ commonRefinedMap X Y)
    (h₂ : f ≫ commonBaseMap X Y = g ≫ commonBaseMap X Y) : f = g := by
  dsimp only [commonRefinedMap, commonBaseMap, commonHom] at *
  exact pullback.hom_ext h₁ h₂

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
