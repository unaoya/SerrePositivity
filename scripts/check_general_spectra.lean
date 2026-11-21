import SerrePositivity.Spectra.General.Foundations
import SerrePositivity.Spectra.General.SimplicialComparison
import SerrePositivity.Spectra.StageTwo
import SerrePositivity.HomotopicalAlgebra.Foundations

universe v u w w'
noncomputable section
open CategoryTheory CategoryTheory.Limits
open SerrePositivity SerrePositivity.GeneralSymmetricSpectrum

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] (K : C)

-- No model structure, pointing, simplicial enrichment, or zero object is needed.
example : Category (GeneralSymmetricSpectrum C K) := inferInstance
example : (forget K).Faithful := inferInstance
example : freeFunctor K ⊣ forget K := freeForgetAdjunction K
example (n : ℕ) : freeAt (K := K) n ⊣ evaluation (K := K) n := freeAtAdjunction n

example (n : ℕ) {X : C} (E : GeneralSymmetricSpectrum C K) (f : X ⟶ level E n) :
    freeAtGenerator (K := K) n X ≫ levelMap (freeAtLift n E f) n = f :=
  freeAtGenerator_lift n E f

-- Naturality in the input and the output uses the actual selected adjunction.
example (n : ℕ) {X X' : C} (a : X ⟶ X') (E : GeneralSymmetricSpectrum C K)
    (f : (freeAt n).obj X' ⟶ E) :
    freeAtHomEquiv n X E ((freeAt n).map a ≫ f) = a ≫ freeAtHomEquiv n X' E f :=
  (freeAtAdjunction n).homEquiv_naturality_left a f

example (n : ℕ) (X : C) {E E' : GeneralSymmetricSpectrum C K} (b : E ⟶ E')
    (f : (freeAt n).obj X ⟶ E) :
    freeAtHomEquiv n X E' (f ≫ b) = freeAtHomEquiv n X E f ≫ levelMap b n :=
  (freeAtAdjunction n).homEquiv_naturality_right f b

variable {J : Type w} [Category.{w'} J]
example : CreatesLimitsOfSize.{w', w} (forget K) := inferInstance
example [HasLimitsOfSize.{0, 0} C] : CreatesColimitsOfSize.{w', w} (forget K) := inferInstance
example [HasLimitsOfShape J C] : HasLimitsOfShape J (GeneralSymmetricSpectrum C K) :=
  inferInstance
example [HasLimitsOfSize.{0, 0} C] [HasColimitsOfShape J C] : HasColimitsOfShape J (GeneralSymmetricSpectrum C K) :=
  inferInstance
example [HasLimitsOfShape J C] (F : J ⥤ GeneralSymmetricSpectrum C K) (n : ℕ) (j : J) :
    (preservesLimitIso (evaluation n) F).hom ≫ limit.π (F ⋙ evaluation n) j =
      levelMap (limit.π F j) n :=
  preservesLimitIso_hom_π (evaluation n) F j
example [HasLimitsOfSize.{0, 0} C] [HasColimitsOfShape J C] (F : J ⥤ GeneralSymmetricSpectrum C K) (n : ℕ) (j : J) :
    levelMap (colimit.ι F j) n ≫ (preservesColimitIso (evaluation n) F).hom =
      colimit.ι (F ⋙ evaluation n) j :=
  ι_preservesColimitIso_hom (evaluation n) F j

-- Coercion-free reuse of the old category, morphisms, free objects and adjunctions.
example (E : SymmetricSpectrum.{u}) :
    GeneralSymmetricSpectrum PointedSimplicialSet.{u} PointedSimplicialSet.circle := E
example {E F : SymmetricSpectrum.{u}} (f : E ⟶ F) :
    levelMap f 0 = f.hom.app (FiniteBijection.of 0) := rfl
example (n : ℕ) :
    SymmetricSpectrum.freeAt.{u} n ⊣ SymmetricSpectrum.evaluation n :=
  freeAtAdjunction (K := PointedSimplicialSet.circle.{u}) n

-- Old enrichment and suspension-loop APIs coexist with the generic entry.
example (X : PointedSimplicialSet.{u}) :
    SymmetricSpectrum.pointwiseTensorFunctor X ⊣ SymmetricSpectrum.cotensorFunctor X :=
  SymmetricSpectrum.pointwiseTensorCotensorAdjunction X

section Closed
variable [HasLimitsOfSize.{0, 0} C]
example : MonoidalClosed (GeneralSymmetricSpectrum C K) := inferInstance
example : SymmetricCategory (GeneralSymmetricSpectrum C K) := inferInstance
example (E X F : GeneralSymmetricSpectrum C K) :
    (tensor E X ⟶ F) ≃ (X ⟶ internalHom E F) := tensorHomEquiv E X F
example {E X F : GeneralSymmetricSpectrum C K} (f : tensor E X ⟶ F) :
    uncurry (curry f) = f := (tensorHomEquiv _ _ _).symm_apply_apply f
example {E X F : GeneralSymmetricSpectrum C K} (f : X ⟶ internalHom E F) :
    curry (uncurry f) = f := (tensorHomEquiv _ _ _).apply_symm_apply f
end Closed

section Structure
open CategoryTheory.MonoidalCategory
example (E : GeneralSymmetricSpectrum C K) (n : ℕ) :
    structureMap E 0 n = (λ_ (level E n)).hom ≫
      E.X.map (FiniteBijection.sumLeftUnitor (FiniteBijection.of n)).inv :=
  structureMap_unit E n
example (E : GeneralSymmetricSpectrum C K) (p q r : ℕ) :
    ((TensorPowers.appendIso K p q).hom ▷ level E r) ≫ structureMap E (p + q) r =
      (α_ (TensorPowers.power K p) (TensorPowers.power K q) (level E r)).hom ≫
        (TensorPowers.power K p ◁ structureMap E q r) ≫ structureMap E p (q + r) ≫
        E.X.map (FiniteBijection.sumAssociator
          (FiniteBijection.of p) (FiniteBijection.of q) (FiniteBijection.of r)).inv :=
  structureMap_assoc E p q r
example (n m : ℕ) (X : C) (h : m < n) :
    IsInitial (level ((freeAt (K := K) n).obj X) m) :=
  SymmetricSequence.freeConvolutionLevelInitial (SymmetricSequence.tensorPowerSequence K) n X m h
example (n m : ℕ) (X : C) :
    level ((freeAt (K := K) n).obj X) m ≅ freeAtLevelBlockQuotient (K := K) n X m :=
  freeAtLevelIsoBlockQuotient n X m
example (n m : ℕ) (X : C) :
    level ((freeAt (K := K) n).obj X) m ≅ colimit (freeAtLevelInductionDiagram (K := K) n X m) :=
  freeAtLevelIsoInduction n X m
end Structure
