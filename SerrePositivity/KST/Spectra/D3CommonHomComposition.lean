module

public import SerrePositivity.KST.Spectra.D3CommonHom
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.EnrichedWhiskeredSquareComposition

/-!
概要：指定比較射を保つ共通 Hom の恒等と実豊穣合成。
方針：元の二段包含と比較の二正方形を、同じ全パラメータで厳密に合成する。
規約：右比較の条件を削除して合成を定めない。
使われ方：d3b② の比較を含む共通解像の豊穣法則。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance commonCompositionSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 二つの元の恒等射を、同じ包含・比較条件の共通 Hom へ束ねる。 -/
def commonIdentity (X : OmegaSpectrum.{u}) : 𝟙_ SSet.{u} ⟶ commonHom X X :=
  commonHomLift X X (mappingIdentity (commonRefinement X)) (fullCompatibleIdentity X)
    (by
      rw [fullCompatibleIdentity_originalMap_assoc]
      simpa only [common_eId] using _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.enriched_whiskered_square_id SSet (commonInclusion X))
    (by
      rw [fullCompatibleIdentity_replacedMap_assoc]
      simpa only [common_eId] using (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.enriched_whiskered_square_id SSet (commonComparison X)).symm)

@[reassoc (attr := simp)]
lemma commonIdentity_refined (X : OmegaSpectrum.{u}) :
    commonIdentity X ≫ commonRefinedMap X X = mappingIdentity (commonRefinement X) :=
  commonHomLift_refined _ _ _ _ _ _

@[reassoc (attr := simp)]
lemma commonIdentity_base (X : OmegaSpectrum.{u}) :
    commonIdentity X ≫ commonBaseMap X X = fullCompatibleIdentity X :=
  commonHomLift_base _ _ _ _ _ _

/-- 二段包含を保つ全 Hom 正方形の合成。 -/
lemma common_composition_left (X Y Z : OmegaSpectrum.{u}) :
    (commonRefinedMap X Y ⊗ₘ commonRefinedMap Y Z) ≫
        mappingComposition (commonRefinement X) (commonRefinement Y) (commonRefinement Z) ≫
        eHomWhiskerRight SSet (commonInclusion X) (commonRefinement Z) =
      (commonBaseMap X Y ⊗ₘ commonBaseMap Y Z) ≫ fullCompatibleComposition X Y Z ≫
        fullOriginalMap X Z ≫ eHomWhiskerLeft SSet X (commonInclusion Z) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.enriched_whiskered_square_comp SSet
    (commonInclusion X) (commonInclusion Y) (commonInclusion Z)
    (commonRefinedMap X Y) (commonOriginalMap X Y)
    (commonRefinedMap Y Z) (commonOriginalMap Y Z)
    (common_left_whiskered X Y) (common_left_whiskered Y Z)
  simpa only [Category.assoc, fullCompatibleComposition_originalMap_assoc,
    ← tensorHom_comp_tensorHom, commonOriginalMap, common_eComp] using h

/-- 同じ全 Hom の合成は元の比較射も厳密に保つ。 -/
lemma common_composition_right (X Y Z : OmegaSpectrum.{u}) :
    (commonRefinedMap X Y ⊗ₘ commonRefinedMap Y Z) ≫
        mappingComposition (commonRefinement X) (commonRefinement Y) (commonRefinement Z) ≫
        eHomWhiskerLeft SSet (commonRefinement X) (commonComparison Z) =
      (commonBaseMap X Y ⊗ₘ commonBaseMap Y Z) ≫ fullCompatibleComposition X Y Z ≫
        fullReplacedMap X Z ≫ eHomWhiskerRight SSet (commonComparison X) (middle Z) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.enriched_whiskered_square_comp SSet
    (commonComparison X) (commonComparison Y) (commonComparison Z)
    (commonMiddleMap X Y) (commonRefinedMap X Y)
    (commonMiddleMap Y Z) (commonRefinedMap Y Z)
    (common_right_whiskered X Y).symm (common_right_whiskered Y Z).symm
  simpa only [Category.assoc, fullCompatibleComposition_replacedMap_assoc,
    ← tensorHom_comp_tensorHom, commonMiddleMap, common_eComp] using h.symm

/-- 元の二つの豊穣合成を、同じ指定二境界を持つ実比較 Hom へ移す。 -/
def commonComposition (X Y Z : OmegaSpectrum.{u}) : commonHom X Y ⊗ commonHom Y Z ⟶
    commonHom X Z :=
  commonHomLift X Z
    ((commonRefinedMap X Y ⊗ₘ commonRefinedMap Y Z) ≫
      mappingComposition (commonRefinement X) (commonRefinement Y) (commonRefinement Z))
    ((commonBaseMap X Y ⊗ₘ commonBaseMap Y Z) ≫ fullCompatibleComposition X Y Z)
    (by simpa only [Category.assoc] using common_composition_left X Y Z)
    (by simpa only [Category.assoc] using common_composition_right X Y Z)

@[reassoc (attr := simp)]
lemma commonComposition_refined (X Y Z : OmegaSpectrum.{u}) :
    commonComposition X Y Z ≫ commonRefinedMap X Z =
      (commonRefinedMap X Y ⊗ₘ commonRefinedMap Y Z) ≫
        mappingComposition (commonRefinement X) (commonRefinement Y) (commonRefinement Z) :=
  commonHomLift_refined _ _ _ _ _ _

@[reassoc (attr := simp)]
lemma commonComposition_base (X Y Z : OmegaSpectrum.{u}) :
    commonComposition X Y Z ≫ commonBaseMap X Z =
      (commonBaseMap X Y ⊗ₘ commonBaseMap Y Z) ≫ fullCompatibleComposition X Y Z :=
  commonHomLift_base _ _ _ _ _ _

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
