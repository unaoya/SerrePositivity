module

public import SerrePositivity.InfinityCategories.F1.Transport.StrictTransportWeightedInverse
public import SerrePositivity.InfinityCategories.F1.Categories.OppositeUnstraighteningHomFamilies
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseRightFilling
public import SerrePositivity.InfinityCategories.F1.Universe.Kan
public import SerrePositivity.InfinityCategories.F1.Universe.QCatEquivalence

/-!
概要：strict transport の像で、元の weighted nerve の全 Hom 作用の同値性を回収する。
方針：構成済みの分類同値の実際の逆写像の充満忠実性を、同じ豊穣 Hom の作用へ戻す。
規約：全 Kan 図式の Hom の Kan 性は主張しない。
使われ方：無条件の反転 Hom 比較から coherent な実際の作用の同値性を得る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

local instance kanDiagramWeightedLiftedProjectionLeftFibration
    {I : Type u} [SmallCategory I] (G : I ⥤ KanObject.{u}) :
    LeftFibration ((SSet.uliftFunctor.{u + 1, u}).map
      (weightedNerveProjection (G ⋙ kanObjectForget))) := by
  have : ∀ i, KanComplex ((G ⋙ kanObjectForget).obj i) := fun i => (G.obj i).isKanComplex
  exact leftFibration_uliftFunctor_map (weightedNerveProjection (G ⋙ kanObjectForget))

local instance strictTransportWeightedSourceKan {I : Type u} [SmallCategory I]
    (F G : StrictTransportDiagramObject I) :
    KanComplex (strictDiagramMappingSpace (F.val ⋙ kanObjectForget) (G.val ⋙ kanObjectForget)) :=
  inferInstanceAs (KanComplex (SimplicialCategory.sHom F G))

local instance strictTransportWeightedTargetKan {I : Type u} [SmallCategory I]
    (F G : StrictTransportDiagramObject I) :
    KanComplex (relativeFunctorSpace (weightedNerveProjection (G.val ⋙ kanObjectForget))
      (weightedNerveProjection (F.val ⋙ kanObjectForget))) :=
  inferInstanceAs (KanComplex (SimplicialCategory.sHom
    ((weightedNerveKanEnriched I).obj (strictTransportKanDiagramEnriched.obj F))
    ((weightedNerveKanEnriched I).obj (strictTransportKanDiagramEnriched.obj G))))

local instance strictTransportWeightedImageSourceKan {I : Type u} [SmallCategory I]
    (F G : StrictTransportDiagramObject I) :
    KanComplex (SimplicialCategory.sHom (strictTransportKanDiagramEnriched.obj F)
      (strictTransportKanDiagramEnriched.obj G)) :=
  inferInstanceAs (KanComplex (SimplicialCategory.sHom F G))

/-- strict transport の像では、元の weighted nerve の全変換空間への作用そのものが同値。 -/
lemma strictTransportWeightedNerveMappingSpaceMap_isQCatEquivalence
    {I : Type u} [SmallCategory I] (F G : StrictTransportDiagramObject I) :
    IsQCatEquivalence (weightedNerveMappingSpaceMap
      (F.val ⋙ kanObjectForget) (G.val ⋙ kanObjectForget)) := by
  let R := strictTransportKanDiagramEnriched.comp SSet (weightedNerveKanEnriched I)
  have hf : IsFullyFaithful (coherentNerveMap R) := by
    change IsFullyFaithful (strictTransportWeightedNerveInfinityMap I)
    exact (leftStrictTransportWeightedNerveEquivalence I).symm.isQCatEquivalence.isFullyFaithful
  have h := (coherentNerveMap_isFullyFaithful_iff R).mp hf F G
  change IsQCatEquivalence (𝟙 _ ≫ weightedNerveMappingSpaceMap
    (F.val ⋙ kanObjectForget) (G.val ⋙ kanObjectForget)) at h
  simpa only [Category.id_comp] using h

/-- 同じ像の共通 Hom 解像で、元の weighted nerve の全パラメーターの作用も同値。 -/
lemma strictTransportCommonWeightedAction_isQCatEquivalence
    {I : Type u} [SmallCategory I] (F G : StrictTransportDiagramObject I) :
    IsQCatEquivalence (kanDiagramCommonWeightedAction
      (strictTransportKanDiagramEnriched.obj F) (strictTransportKanDiagramEnriched.obj G)) := by
  let F' := strictTransportKanDiagramEnriched.obj F
  let G' := strictTransportKanDiagramEnriched.obj G
  have : KanComplex (SimplicialCategory.sHom F' G') :=
    inferInstanceAs (KanComplex (SimplicialCategory.sHom F G))
  have he := IsQCatEquivalence.ulift.{u, u + 1}
    (isQCatEquivalence_of_trivialKanFibration (edgewiseRight (SimplicialCategory.sHom F' G')))
  have hw := IsQCatEquivalence.ulift.{u, u + 1}
    (strictTransportWeightedNerveMappingSpaceMap_isQCatEquivalence F G)
  exact he.comp (hw.comp (qCatEquivalenceOfIso
    (uliftRelativeFunctorIso.{u, u + 1} (weightedNerveProjection (G.val ⋙ kanObjectForget))
      (weightedNerveProjection (F.val ⋙ kanObjectForget)))).isQCatEquivalence)

end SerrePositivity.InfinityCategories
