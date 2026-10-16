module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.MappingPrecompositionRetraction
public import SerrePositivity.HomotopicalAlgebra.Simplicial.PushoutInternalHomPullback
public import SerrePositivity.HomotopicalAlgebra.Simplicial.HomotopyRetractionTests
public import SerrePositivity.HomotopicalAlgebra.Simplicial.MonoRightLiftingContraction
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanTestDetection

/-! # Push out a boundary-right map along an arbitrary mono

The internal-Hom square is the actual Kan pullback of a strong deformation
retract. Unit-valued postcomposition classes recover the original Kan
tests. No source or target of the original square is assumed Kan.
-/

@[expose] public section
universe v
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace SerrePositivity.SimplicialModel.MonoRightPushoutEquivalence
variable {A B C P : SSet.{v}} (p : A ⟶ B)
  (hp : (MorphismProperty.monomorphisms SSet.{v}).rlp p)
  (j : A ⟶ C) [Mono j] (u : B ⟶ P) (g : C ⟶ P) (sq : IsPushout p j u g)

include hp sq in
lemma tests : KanTestDetection.Tests g := by
  obtain ⟨s, hs⟩ := MonoRightLiftingContraction.exists_section p hp
  obtain ⟨H, hH⟩ := MonoRightLiftingContraction.exists_vertical_contraction p hp s hs
  intro K hK
  have : Fibration (terminal.from K) := (SSet.modelCategoryQuillen.fibration_iff _).mpr hK
  have : SSet.KanComplex K := (isFibrant_iff K).mpr inferInstance
  have hq : SSet.modelCategoryQuillen.J.rlp ((MonoidalClosed.pre j).app K) :=
    (SSet.modelCategoryQuillen.fibration_iff _).mp inferInstance
  obtain ⟨r, hr, V, _⟩ := KanPullbackDeformation.exists_retraction
    ((MonoidalClosed.pre p).app K) ((MonoidalClosed.pre s).app K)
    (MappingPrecompositionRetraction.retraction p s hs K)
    (MappingPrecompositionRetraction.homotopy p s H K)
    (MappingPrecompositionRetraction.fixed p s H hH K)
    ((MonoidalClosed.pre j).app K) hq ((MonoidalClosed.pre g).app K)
    ((MonoidalClosed.pre u).app K) (PushoutInternalHomPullback.isPullback sq K).flip
  exact HomotopyRetractionTests.pre_bijective_of_restriction_post g
    (HomotopyRetractionTests.post_bijective _ r hr V (𝟙_ SSet.{v}))

include hp sq in
lemma localized_isIso : IsIso (AnodyneHomotopy.anodyneQ.map g) :=
  (KanTestDetection.anodyneQ_isIso_iff_tests g).mpr (tests p hp j u g sq)

end SerrePositivity.SimplicialModel.MonoRightPushoutEquivalence
