module

public import SerrePositivity.KST.Spectra.D3CommonEnrichment
public import SerrePositivity.KST.Spectra.StrictEnrichedTransformationNerve

/-!
概要：共通比較射を保持する全 Hom の豊穣構造を、元の Sp の全図式比較へ送る。
方針：実全 Hom の RLP と厳密自然性、元の成分の全段 π 同型を適用する。
規約：この全図式比較は共通 BF 解像と元の BF 解像の間。nativeLoop との比較は未完。
使われ方：d3b② の比較射を含む Hom の coherent な接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance commonCoherentSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance commonCoherentHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y

/-- 共通解像から元の Sp への全単体射影。 -/
def commonOriginalInfinityMap : SimplicialNerve CommonObject ⟶ Sp.{u} :=
  coherentNerveMap commonOriginalEnriched

/-- 比較射を含めた全 Hom の元の Sp への回収は完全忠実。 -/
lemma commonOriginalInfinityMap_isFullyFaithful : IsFullyFaithful commonOriginalInfinityMap := by
  apply (coherentNerveMap_isFullyFaithful_iff commonOriginalEnriched).mpr
  intro X Y
  exact (qCatEquivalenceOfTrivialKanFibration (commonOriginalMap X.val Y.val)).isQCatEquivalence

/-- 同じ元の対象を包む射影は元の全頂点を回収する。 -/
lemma commonOriginalInfinityMap_isEssentiallySurjective :
    IsEssentiallySurjective commonOriginalInfinityMap := by
  intro y
  refine ⟨coherentNerveVertex (⟨coherentNerveObject y⟩ : CommonObject), ?_⟩
  change Nonempty (VertexIso
    ((coherentNerveMap commonOriginalEnriched).app _ (coherentNerveVertex _)) y)
  rw [coherentNerveMap_vertex]
  exact ⟨eqToIso (congrArg SSet.HomotopyCategory.mk (coherentNerveVertex_object y))⟩

/-- 比較を含む同じ共通解像と元の Sp の実同値。 -/
def commonOriginalInfinityEquivalence : QCatEquivalence (SimplicialNerve CommonObject) Sp.{u} :=
  qCatEquivalenceOfFullyFaithfulEssentiallySurjective commonOriginalInfinityMap
    commonOriginalInfinityMap_isFullyFaithful commonOriginalInfinityMap_isEssentiallySurjective

/-- 元の二段包含を成分とする厳密な豊穣自然変換。 -/
def commonGradedInclusion :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u}))
      commonOriginalEnriched commonRefinedEnriched where
  app X := eHomEquiv SSet (commonInclusion X.val)
  naturality X Y := ((_root_.SerrePositivity.InfinityCategories.Kan.enriched_whiskered_square_iff SSet
    (commonInclusion X.val) (commonInclusion Y.val)
    (commonRefinedMap X.val Y.val) (commonOriginalMap X.val Y.val)).mp
      (common_left_whiskered X.val Y.val)).symm

/-- 元の指定比較右脚を成分とする厳密な豊穣自然変換。 -/
def commonGradedComparison :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u}))
      commonRefinedEnriched commonMiddleEnriched where
  app X := eHomEquiv SSet (commonComparison X.val)
  naturality X Y := ((_root_.SerrePositivity.InfinityCategories.Kan.enriched_whiskered_square_iff SSet
    (commonComparison X.val) (commonComparison Y.val)
    (commonMiddleMap X.val Y.val) (commonRefinedMap X.val Y.val)).mp
      (common_right_whiskered X.val Y.val).symm).symm

/-- 移送した包含の成分も元の二段左脚そのもの。 -/
lemma commonInclusion_componentHom (X : CommonObject) :
    StrictEnrichedTransformation.componentHom commonOriginalEnriched commonRefinedEnriched
      commonGradedInclusion X = commonInclusion X.val := by
  change (SimplicialCategory.homEquiv' _ _).symm
    ((SSet.unitHomEquiv _) (eHomEquiv SSet (commonInclusion X.val))) = _
  exact Equiv.symm_apply_apply _ _

/-- 移送した比較の成分も元の全段 RLP を持つ同じ右脚。 -/
lemma commonComparison_componentHom (X : CommonObject) :
    StrictEnrichedTransformation.componentHom commonRefinedEnriched commonMiddleEnriched
      commonGradedComparison X = commonComparison X.val := by
  change (SimplicialCategory.homEquiv' _ _).symm
    ((SSet.unitHomEquiv _) (eHomEquiv SSet (commonComparison X.val))) = _
  exact Equiv.symm_apply_apply _ _

/-- 指定二段包含を保つ、元の Sp と共通 BF 対象の全図式同型。 -/
def commonInclusionFunctorIso :
    FunctorIso (coherentNerveMap commonOriginalEnriched) (coherentNerveMap commonRefinedEnriched) :=
  StrictEnrichedTransformation.functorIso commonOriginalEnriched commonRefinedEnriched
    commonGradedInclusion (fun X ↦ by
      rw [commonInclusion_componentHom]
      exact isInvertible_of_piIsomorphism _
        (piIsomorphism_of_levelwise _ (commonInclusion_levelwise X.val)))

/-- 指定比較右脚を保つ、共通 BF 対象と元の相対 BF 対象の全図式同型。 -/
def commonComparisonFunctorIso :
    FunctorIso (coherentNerveMap commonRefinedEnriched) (coherentNerveMap commonMiddleEnriched) :=
  StrictEnrichedTransformation.functorIso commonRefinedEnriched commonMiddleEnriched
    commonGradedComparison (fun X ↦ by
      rw [commonComparison_componentHom]
      exact isInvertible_of_piIsomorphism _
        (piIsomorphism_of_levelwise _ (commonComparison_levelwise X.val)))

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
