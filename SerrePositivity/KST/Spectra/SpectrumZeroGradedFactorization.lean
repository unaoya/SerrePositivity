module

public import SerrePositivity.KST.Spectra.RawSpectrumPointedBasepointComposition
public import SerrePositivity.KST.Spectra.SpectrumCotensorEvaluationRestriction
public import SerrePositivity.KST.Spectra.SpectrumZeroObject

/-!
概要：cotensor の基点での零評価の、実際の零対象経由の豊穣自然な因子分解。
方針：一点スペクトルを値とする豊穣関手を入れ、両側の Hom の終対象性で自然性を示す。
規約：成分の因子分解は元の零評価との厳密な等式。
使われ方：二つの零角を持つ loop 四角形の三角形を構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet

namespace SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
local instance zeroGradedSpectrumSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 一点スペクトルを値とする、元の整合写像の圏上の豊穣関手。 -/
def zeroEnriched (A : PointedSimplicialSet.{u}) :
    EnrichedFunctor SSet.{u} (Object A) OmegaSpectrum.{u} where
  obj _ := _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint
  map _ _ := toUnit _ ≫ mappingIdentity _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint
  map_id _ := (mappingPoint_isTerminal _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint).hom_ext _ _
  map_comp _ _ _ := (mappingPoint_isTerminal _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint).hom_ext _ _

/-- cotensor 側から一点スペクトルへの、全 Hom パラメータで自然な射。 -/
def toZeroEvaluation (A : PointedSimplicialSet.{u}) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) (cotensorEnriched A) (zeroEnriched A) where
  app X := (RawSpectrumMapping.pointedSpace (cotensor A X.val) _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint.toKanSequence).hom
  naturality X _ := (mappingPoint_isTerminal (cotensor A X.val)).hom_ext _ _

/-- 一点スペクトルから元の対象への、全 Hom パラメータで自然な射。 -/
def fromZeroEvaluation (A : PointedSimplicialSet.{u}) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) (zeroEnriched A) (sourceEnriched A) where
  app X := (RawSpectrumMapping.pointedSpace _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint X.val.toKanSequence).hom
  naturality _ Y := (pointMapping_isTerminal Y.val).hom_ext _ _

/-- 二つの自然な零対象の射の合成は、元の評価を基点へ制限した族に厳密一致。 -/
lemma zeroEvaluation_factorization (A : PointedSimplicialSet.{u}) (X : Object A) :
    (λ_ (𝟙_ SSet.{u})).inv ≫
        ((toZeroEvaluation A).app X ⊗ₘ (fromZeroEvaluation A).app X) ≫
          mappingComposition (cotensor A X.val) _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint X.val =
      (parameterEvaluation A A.hom).app X := by
  rw [parameterEvaluation_basepoint]
  exact RawSpectrumMapping.basepoint_composition (cotensor A X.val) _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint
    X.val.toKanSequence

end SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
