module

public import SerrePositivity.InfinityCategories.ModelBridge.QuillenCfCollageInclusions
public import SerrePositivity.InfinityCategories.F1.Coherent.NerveFullyFaithful
public import SerrePositivity.InfinityCategories.F1B.MappingSpaces.IntervalFunctorMap
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.RightIntervalEquivalence

/-!
概要：元の cf 包含の写像空間上の充満忠実性。
方針：豊穣 Hom の恒等写像を coherent nerve の比較で移し、区間模型にも戻す。
規約：元の包含を保持。使われ方：Quillen 導来単位の写像空間条件。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory HomotopicalAlgebra MonoidalCategory SSet
open SerrePositivity.InfinityCategories.Coherent
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
/-- 充満忠実な元の写像は、区間模型でも写像空間のホモトピー同値を誘導する。 -/
lemma intervalFunctorMap_isSimplicialHomotopyEquivalence_of_fullyFaithful
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (f : X ⟶ Y) (hf : IsFullyFaithful f) (x y : X _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (intervalFunctorMap f x y) := by
  have hc := (SerrePositivity.InfinityCategories.pinchedHomToIntervalMappingSpace_isQCatEquivalence x y)
  have hd := SerrePositivity.InfinityCategories.pinchedHomToIntervalMappingSpace_isQCatEquivalence
    (f.app (Opposite.op ⦋0⦌) x) (f.app (Opposite.op ⦋0⦌) y)
  have h := (hf x y).isQCatEquivalence.comp hd
  rw [pinchedIntervalComparison_naturality] at h
  exact (hc.cancel_left h).isSimplicialHomotopyEquivalence
variable {C D : Type v} [Category.{u} C] [Category.{u} D]
  [ModelCategory C] [ModelCategory D] [SimplicialCategory C] [SimplicialCategory D]
  (R : EnrichedFunctor SSet.{u} D C) {L : C ⥤ D}
  (adj : L ⊣ coherentEnrichedUnderlyingFunctor R) [SerrePositivity.Quillen.IsLeftQuillen L]
  (SC : SerrePositivity.Enriched.TensorCotensor SSet.{u} C)
  (SD : SerrePositivity.Enriched.TensorCotensor SSet.{u} D)
  [FixedSimplicialPushoutProduct SC.tensor] [FixedSimplicialPushoutProduct SD.tensor]
include adj SC SD in
/-- 元の下段 cf 包含は、全写像空間の意味で充満忠実である。 -/
lemma quillenCfCollageBottomNerve_isFullyFaithful : IsFullyFaithful
    (quillenCfCollageBottomNerve R) := by
  have : ∀ X Y : CofibrantFibrantObjects C, KanComplex (SimplicialCategory.sHom X Y) :=
    cofibrantFibrantObjects_sHom_kanComplex SC
  have : ∀ X Y : QuillenCfCollage R, KanComplex (SimplicialCategory.sHom X Y) :=
    quillenCfCollage_sHom_kanComplex R adj SC SD
  apply (coherentNerveMap_isFullyFaithful_iff (quillenCfCollageBottom R)).mpr
  intro X Y
  change IsQCatEquivalence (𝟙 (SimplicialCategory.sHom X.obj Y.obj))
  exact (QCatEquivalence.refl _).isQCatEquivalence
include adj SC SD in
/-- 元の上段 cf 包含も、同じ全写像空間の意味で充満忠実である。 -/
lemma quillenCfCollageTopNerve_isFullyFaithful : IsFullyFaithful
    (quillenCfCollageTopNerve R) := by
  have : ∀ X Y : CofibrantFibrantObjects D, KanComplex (SimplicialCategory.sHom X Y) :=
    cofibrantFibrantObjects_sHom_kanComplex SD
  have : ∀ X Y : QuillenCfCollage R, KanComplex (SimplicialCategory.sHom X Y) :=
    quillenCfCollage_sHom_kanComplex R adj SC SD
  apply (coherentNerveMap_isFullyFaithful_iff (quillenCfCollageTop R)).mpr
  intro X Y
  change IsQCatEquivalence (𝟙 (SimplicialCategory.sHom X.obj Y.obj))
  exact (QCatEquivalence.refl _).isQCatEquivalence

end
end SerrePositivity.InfinityCategories.HomotopyLimits
