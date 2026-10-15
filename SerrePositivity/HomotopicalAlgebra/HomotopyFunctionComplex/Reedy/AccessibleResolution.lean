module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.AccessibleFactorization
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.FunctorialResolution

/-! # Accessibility of the actual functorial Reedy resolution families -/

@[expose] public section
universe w v u v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] {C : Type u'} [Category.{v'} C] [ModelCategory C]
  [IsLocallyPresentable.{w} C]

omit [ModelCategory C] [IsLocallyPresentable.{w} C] in
lemma constantDiagram_isCardinalAccessible (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    (Functor.const J : C ⥤ J ⥤ C).IsCardinalAccessible κ := by
  have : ∀ j, Functor.IsCardinalAccessible
      ((Functor.const J : C ⥤ J ⥤ C) ⋙ (evaluation J C).obj j) κ :=
    fun _ ↦ inferInstanceAs ((𝟭 C).IsCardinalAccessible κ)
  exact Smith.AccessibleColimits.functorCategory_isCardinalAccessible _ κ

omit [IsLocallyPresentable.{w} C] in
lemma initialConstantArrows_isAccessible :
    (initialConstantArrows (J := J) (C := C)).IsAccessible.{w} := by
  let κ : Cardinal.{w} := Cardinal.aleph0
  have : Fact κ.IsRegular := Cardinal.fact_isRegular_aleph0
  have hconst := constantDiagram_isCardinalAccessible (J := J) (C := C) κ
  have : (initialConstantArrows (J := J) (C := C) ⋙ Arrow.leftFunc).IsCardinalAccessible κ :=
    Smith.constant_isCardinalAccessible (D := C) (⊥_ (J ⥤ C)) κ
  have : (initialConstantArrows (J := J) (C := C) ⋙ Arrow.rightFunc).IsCardinalAccessible κ :=
    hconst
  have := Smith.AccessibleFactorization.arrowFunctor_isCardinalAccessible
    (initialConstantArrows (J := J) (C := C)) κ
  exact Functor.isAccessible_of_isCardinalAccessible _ κ

omit [IsLocallyPresentable.{w} C] in
lemma terminalConstantArrows_isAccessible :
    (terminalConstantArrows (J := J) (C := C)).IsAccessible.{w} := by
  let κ : Cardinal.{w} := Cardinal.aleph0
  have : Fact κ.IsRegular := Cardinal.fact_isRegular_aleph0
  have hconst := constantDiagram_isCardinalAccessible (J := J) (C := C) κ
  have : (terminalConstantArrows (J := J) (C := C) ⋙ Arrow.leftFunc).IsCardinalAccessible κ :=
    hconst
  have : (terminalConstantArrows (J := J) (C := C) ⋙ Arrow.rightFunc).IsCardinalAccessible κ :=
    Smith.constant_isCardinalAccessible (D := C) (⊤_ (J ⥤ C)) κ
  have := Smith.AccessibleFactorization.arrowFunctor_isCardinalAccessible
    (terminalConstantArrows (J := J) (C := C)) κ
  exact Functor.isAccessible_of_isCardinalAccessible _ κ

variable {inverse direct : MorphismProperty J} [inverse.IsMultiplicative] [direct.IsMultiplicative]
  (r : ReedyStructure inverse direct ℕ) [Small.{w} J]
  [∀ j, HasColimitsOfShape (LatchingIndex r j) C]
  [∀ j, HasLimitsOfShape (MatchingIndex r j) C]
  [∀ j, EssentiallySmall.{w} (MatchingIndex r j)]
  (hinj : Function.Injective r.deg) (hsurj : Function.Surjective r.deg)

lemma cofibrantResolutionFamily_isAccessible
    (source : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    [source.Z.IsAccessible.{w}] :
    (cofibrantResolutionFamily r hinj hsurj source).obj.IsAccessible.{w} := by
  have := initialConstantArrows_isAccessible.{w} (J := J) (C := C)
  have := FunctorFactorizationSequence.middleFunctor_isAccessible.{w} r hinj source hsurj
  exact inferInstanceAs ((initialConstantArrows (J := J) (C := C) ⋙
    FunctorFactorizationSequence.middleFunctor r hinj hsurj source).IsAccessible.{w})

lemma fibrantResolutionFamily_isAccessible
    (source : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    [source.Z.IsAccessible.{w}] :
    (fibrantResolutionFamily r hinj hsurj source).obj.IsAccessible.{w} := by
  have := terminalConstantArrows_isAccessible.{w} (J := J) (C := C)
  have := FunctorFactorizationSequence.middleFunctor_isAccessible.{w} r hinj source hsurj
  exact inferInstanceAs ((terminalConstantArrows (J := J) (C := C) ⋙
    FunctorFactorizationSequence.middleFunctor r hinj hsurj source).IsAccessible.{w})

end SerrePositivity.Reedy
