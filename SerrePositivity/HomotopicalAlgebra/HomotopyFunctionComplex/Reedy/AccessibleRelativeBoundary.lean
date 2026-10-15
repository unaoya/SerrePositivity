module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.AccessibleBoundary
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.FunctorFactorizationFamily
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.RelativeBoundaryFunctor
public import SerrePositivity.HomotopicalAlgebra.Smith.AccessiblePushoutPullback
public import SerrePositivity.HomotopicalAlgebra.Smith.AccessibleFactorization

/-! # Accessibility of the actual relative boundary arrow at one Reedy step -/

@[expose] public section
universe w v u v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Smith.AccessiblePushoutPullback

namespace SerrePositivity.Reedy.FunctorFactorAt
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  (r : ReedyStructure inverse direct ℕ) (j : J) {C : Type u'} [Category.{v'} C]
  [HasColimitsOfShape (LatchingIndex r j) C] [HasLimitsOfShape (MatchingIndex r j) C]
  [HasPushouts C] [HasPullbacks C]
  (a : FunctorFactorAt (C := C) r (r.deg j))

abbrev originalLatching :
    (Arrow.leftFunc : Arrow (J ⥤ C) ⥤ J ⥤ C) ⋙ restrictionFunctor r (r.deg j) ⋙
        lowerLatchingEvaluation r j ⟶ Arrow.leftFunc ⋙ (evaluation J C).obj j :=
  Functor.whiskerLeft (Arrow.leftFunc ⋙ BoundaryDiagram.fromFunctor r j C)
    (BoundaryDiagram.latchingComparison r j C)

abbrev originalMatching :
    (Arrow.rightFunc : Arrow (J ⥤ C) ⥤ J ⥤ C) ⋙ (evaluation J C).obj j ⟶
      Arrow.rightFunc ⋙ restrictionFunctor r (r.deg j) ⋙ lowerMatchingEvaluation r j :=
  Functor.whiskerLeft (Arrow.rightFunc ⋙ BoundaryDiagram.fromFunctor r j C)
    (BoundaryDiagram.matchingComparison r j C)

abbrev relativeDomainPresentation :=
  pointwisePushout (Functor.whiskerRight a.i (lowerLatchingEvaluation r j)) (originalLatching r j)

abbrev relativeCodomainPresentation :=
  pointwisePullback (originalMatching r j)
    (Functor.whiskerRight a.p (lowerMatchingEvaluation r j))

abbrev relativeArrow : Arrow (J ⥤ C) ⥤ Arrow C :=
  a.problemFunctor r j ⋙ FactorizationProblem.relativeBoundaryFunctor r j C

def relativeDomainIso : relativeDomainPresentation r j a ≅ relativeArrow r j a ⋙ Arrow.leftFunc :=
  eqToIso (by rfl)

def relativeCodomainIso :
    relativeCodomainPresentation r j a ≅ relativeArrow r j a ⋙ Arrow.rightFunc :=
  eqToIso (by rfl)

private lemma accessible_of_preserves {B : Type*} [Category* B] {E : Type*} [Category* E]
    (F : B ⥤ E) [PreservesColimitsOfSize.{w, w} F] : F.IsAccessible.{w} := by
  have : Fact Cardinal.aleph0.IsRegular := Cardinal.fact_isRegular_aleph0
  exact F.isAccessible_of_isCardinalAccessible Cardinal.aleph0

lemma relativeArrow_isAccessible [IsLocallyPresentable.{w} C]
    [EssentiallySmall.{w} (MatchingIndex r j)] [a.Z.IsAccessible.{w}] :
    (relativeArrow r j a).IsAccessible.{w} := by
  have : HasColimitsOfSize.{w, w} C := Smith.locallyPresentable_hasColimits (C := C)
  have : Fact Cardinal.aleph0.IsRegular := Cardinal.fact_isRegular_aleph0
  have hLκ := Smith.AccessibleFactorization.arrow_left_isCardinalAccessible
    (C := J ⥤ C) (Cardinal.aleph0 : Cardinal.{w})
  have hRκ := Smith.AccessibleFactorization.arrow_right_isCardinalAccessible
    (C := J ⥤ C) (Cardinal.aleph0 : Cardinal.{w})
  have hL := Functor.isAccessible_of_isCardinalAccessible
    (Arrow.leftFunc : Arrow (J ⥤ C) ⥤ (J ⥤ C)) (Cardinal.aleph0 : Cardinal.{w})
  have hR := Functor.isAccessible_of_isCardinalAccessible
    (Arrow.rightFunc : Arrow (J ⥤ C) ⥤ (J ⥤ C)) (Cardinal.aleph0 : Cardinal.{w})
  have hres := accessible_of_preserves.{w} (restrictionFunctor (C := C) r (r.deg j))
  have hevκ : ((evaluation J C).obj j).IsCardinalAccessible (Cardinal.aleph0 : Cardinal.{w}) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  have hev := Functor.isAccessible_of_isCardinalAccessible ((evaluation J C).obj j)
    (Cardinal.aleph0 : Cardinal.{w})
  have hlat := lowerLatchingEvaluation_isCardinalAccessible (C := C) r j
    (Cardinal.aleph0 : Cardinal.{w})
  have hlat' := Functor.isAccessible_of_isCardinalAccessible
    (lowerLatchingEvaluation (C := C) r j) (Cardinal.aleph0 : Cardinal.{w})
  have hmat := lowerMatchingEvaluation_isAccessible.{w} (C := C) r j
  have hdom := pointwisePushout_isAccessible.{w}
    (Functor.whiskerRight a.i (lowerLatchingEvaluation r j)) (originalLatching r j)
  have hcod := pointwisePullback_isAccessible.{w} (originalMatching r j)
    (Functor.whiskerRight a.p (lowerMatchingEvaluation r j))
  obtain ⟨κL, hκL, hL'⟩ := Functor.IsAccessible.exists_cardinal (relativeDomainPresentation r j a)
  obtain ⟨κR, hκR, hR'⟩ := Functor.IsAccessible.exists_cardinal (relativeCodomainPresentation r j a)
  obtain ⟨κ, hκ, hLκ, hRκ⟩ := Cardinal.SharplyLT.exists_of_pair κL κR
  have := Functor.isCardinalAccessible_of_le (relativeDomainPresentation r j a) hLκ.le
  have := Functor.isCardinalAccessible_of_le (relativeCodomainPresentation r j a) hRκ.le
  have := Functor.isCardinalAccessible_of_natIso (relativeDomainIso r j a) κ
  have := Functor.isCardinalAccessible_of_natIso (relativeCodomainIso r j a) κ
  have := Smith.AccessibleFactorization.arrowFunctor_isCardinalAccessible (relativeArrow r j a) κ
  exact Functor.isAccessible_of_isCardinalAccessible _ κ

end SerrePositivity.Reedy.FunctorFactorAt
