module
public import SerrePositivity.KST.SConstruction.DGKFixedInterface
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFSOASpectrumComparison

/-! # 固定 ν の元の S• と固定 K の対象・射の同定
概要：ν(P) の境界商から、同じ K(P) の全正段への前向き弱比較を公開する。
方針：元の商の Ex∞ 単位と、既存の実 BF 段の比較を合成する。
規約：零段は同じ境界商の loop。使われ方：K-F の相対 S• 定理を固定 K へ移す。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
variable (A : Type u) [CommRing A]

local instance fixedSConstruction_simplicialCategory :
    SimplicialCategory OmegaSpectrum.{w} := OmegaSpectrum.simplicialCategory

/-- 固定 ν(P) の元の r 次 S• 境界商。 -/
abbrev dgKInputSBoundary (r : ℕ) (P : PerfDGInput.{u, v} A) :=
  boundaryReducedRealization r (stableCategoryModel (dgKInputStableValue A P))

/-- ν(P) の元の境界商から K(P) の正段への同じ実比較。 -/
def dgKInputSBoundaryComparison (r : ℕ) (P : PerfDGInput.{u, v} A) :
    dgKInputSBoundary A r P ⟶ ((dgKInputSpectrum A P).level (r + 1)).space :=
  presentedPerfectDGBoundaryKanUnit A r P ≫
    (presentedPerfectDGBFPositiveStage A r).comparison P

/-- 元の境界商から正段への比較は anodyne 局所化で可逆。 -/
lemma dgKInputSBoundaryComparison_localized_isIso (r : ℕ) (P : PerfDGInput.{u, v} A) :
    IsIso (AnodyneHomotopy.anodyneQ.map (dgKInputSBoundaryComparison A r P).right) := by
  letI hu := (Localization.inverts AnodyneHomotopy.anodyneQ anodyneExtensions)
    (presentedPerfectDGBoundaryKanUnit A r P).right
    (presentedPerfectDGBoundaryKanUnit_anodyne A r P)
  have hc := (presentedPerfectDGBFPositiveStage A r).weak P
  change IsIso (AnodyneHomotopy.anodyneQ.map
    ((presentedPerfectDGBoundaryKanUnit A r P).right ≫ _))
  rw [Functor.map_comp]
  exact IsIso.comp_isIso' hu hc

/-- 元の商の Kan 値から固定 K の正段への比較は、同じ BF 射と厳密に可換。 -/
lemma dgKInputSBoundaryKanComparison_naturality (r : ℕ)
    {P Q : PerfDGInput.{u, v} A} (f : P ⟶ Q) :
    (presentedPerfectDGBoundaryKanMap A r f).hom ≫
        (show ((presentedPerfectDGBFBoundaryFunctor A r).obj Q).obj ⟶
          ((dgKInputSpectrum A Q).level (r + 1)).space from
            (presentedPerfectDGBFPositiveStage A r).comparison Q) =
      (show ((presentedPerfectDGBFBoundaryFunctor A r).obj P).obj ⟶
        ((dgKInputSpectrum A P).level (r + 1)).space from
          (presentedPerfectDGBFPositiveStage A r).comparison P) ≫
            (dgKInputSpectrumMap A f).app (r + 1) := by
  rw [presentedPerfectDGBFMap_positive_app]
  exact presentedPerfectDGBFStageComparison_naturality A r
    (presentedPerfectDGBFPositiveStage A r) f

/-- 元の S• 境界商からの同じ弱比較は、置換前の元の射にも厳密に自然。 -/
lemma dgKInputSBoundaryComparison_naturality (r : ℕ)
    {P Q : PerfDGInput.{u, v} A} (f : P ⟶ Q) :
    boundaryReducedRealizationMap r (presentedPerfectDGBFInputStableMap A f) ≫
        dgKInputSBoundaryComparison A r Q =
      dgKInputSBoundaryComparison A r P ≫ (dgKInputSpectrumMap A f).app (r + 1) := by
  have hu := exInfinityPointedUnit_naturality (presentedPerfectDGBoundaryPointedMap A r f)
  have hc := dgKInputSBoundaryKanComparison_naturality A r f
  change _ ≫ (presentedPerfectDGBoundaryKanUnit A r Q ≫ _) =
    (presentedPerfectDGBoundaryKanUnit A r P ≫ _) ≫ _
  have hu' : boundaryReducedRealizationMap r (presentedPerfectDGBFInputStableMap A f) ≫
      presentedPerfectDGBoundaryKanUnit A r Q =
    presentedPerfectDGBoundaryKanUnit A r P ≫ (presentedPerfectDGBoundaryKanMap A r f).hom :=
    hu.symm
  erw [← Category.assoc, hu', Category.assoc, hc, ← Category.assoc]

/-- 固定 K の零段は ν(P) の同じ元の境界商の Ex∞ loop。 -/
lemma dgKInputSpectrum_zero (P : PerfDGInput.{u, v} A) :
    ((dgKInputSpectrum A P).level 0).space =
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace ((presentedPerfectDGBoundaryKanEnrichedFunctor A 0).obj P).obj :=
  presentedPerfectDGBFOmegaSpectrum_zero A P

/-- 固定 K の零段の辺も、ν の元の S• 境界商射の loop を厳密に回収する。 -/
lemma dgKInputSpectrumMap_zero {P Q : PerfDGInput.{u, v} A} (f : P ⟶ Q) :
    (dgKInputSpectrumMap A f).app 0 =
      (PointedObject.basedHomFunctor PointedSimplicialSet.circle.{max (u + 1) v}).map
        (presentedPerfectDGBoundaryKanMap A 0 f).hom :=
  presentedPerfectDGBFMap_zero_app A f

/-- ν(P) の旧 SOA S• スペクトルから同じ固定 K(P) への実 BF 比較。 -/
def dgKInputSOAComparison (P : PerfDGInput.{u, v} A) :
    kOmegaSpectrum (stableCategoryModel (dgKInputStableValue A P)) ⟶ dgKInputSpectrum A P :=
  presentedPerfectDGBFSOASpectrumComparison A P

/-- 同じ旧 SOA との実 BF 比較は Sp の可逆辺を与える。 -/
lemma dgKInputSOAComparison_isInvertible (P : PerfDGInput.{u, v} A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKInputSOAComparison A P)) :=
  OmegaSpectrum.isInvertible_of_piIsomorphism _
    (presentedPerfectDGBFSOASpectrumComparison_piIsomorphism A P)

end SerrePositivity.KST.SConstruction
