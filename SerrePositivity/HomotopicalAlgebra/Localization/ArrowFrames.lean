module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionComparison
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FramePreservation

/-! # Natural Reedy-cofibrant frame representatives of arbitrary arrows

Resolve both ends of every original arrow, and factor the actual map of
resolutions in the constructed Reedy model. The resulting source and
target are frames, the frame map is a Reedy cofibration, and its two
augmentations form actual weak squares over the original arrow.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.Bousfield.ArrowFrames
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))

abbrev resolution := (cosimplicialResolutionFamily cof).obj
abbrev resolvedArrows : Arrow C ⥤ Arrow (SimplexCategory ⥤ C) := (resolution cof).mapArrow

abbrev source : Arrow C ⥤ SimplexCategory ⥤ C := Arrow.leftFunc ⋙ resolution cof

abbrev target : Arrow C ⥤ SimplexCategory ⥤ C := by
  let := simplexModelCategory C
  exact resolvedArrows cof ⋙ (ResolutionComparison.diagramCofFactorization cof).Z

def inclusion : source cof ⟶ target cof := by
  let := simplexModelCategory C
  exact Functor.whiskerLeft (resolvedArrows cof)
    (ResolutionComparison.diagramCofFactorization cof).i

def projection : target cof ⟶ Arrow.rightFunc ⋙ resolution cof := by
  let := simplexModelCategory C
  exact Functor.whiskerLeft (resolvedArrows cof)
    (ResolutionComparison.diagramCofFactorization cof).p

def sourceAugmentation : source cof ⟶ Arrow.leftFunc ⋙ Functor.const SimplexCategory :=
  Functor.whiskerLeft Arrow.leftFunc (cosimplicialResolutionFamily cof).augmentation

def targetAugmentation : target cof ⟶ Arrow.rightFunc ⋙ Functor.const SimplexCategory :=
  projection cof ≫
    Functor.whiskerLeft Arrow.rightFunc (cosimplicialResolutionFamily cof).augmentation

lemma factorization (f : Arrow C) :
    (inclusion cof).app f ≫ (projection cof).app f = (resolution cof).map f.hom := by
  let := simplexModelCategory C
  exact (ResolutionComparison.diagramCofFactorization cof).fac_app

lemma inclusion_reedyCofibration (f : Arrow C) :
    reedyLeft simplex (cofibrations C) ((inclusion cof).app f) := by
  let := simplexModelCategory C
  exact (ResolutionComparison.diagramCofFactorization cof).hi ((resolvedArrows cof).obj f)

lemma projection_weakEquivalence (f : Arrow C) (n : SimplexCategory) :
    weakEquivalences C (((projection cof).app f).app n) := by
  let := simplexModelCategory C
  exact ((ResolutionComparison.diagramCofFactorization cof).hp ((resolvedArrows cof).obj f)).2 n

lemma source_reedyCofibrant (f : Arrow C) :
    reedyLeft simplex (cofibrations C) (initial.to ((source cof).obj f)) :=
  (cosimplicialResolutionFamily cof).cofibrant f.left

lemma target_reedyCofibrant (f : Arrow C) :
    reedyLeft simplex (cofibrations C) (initial.to ((target cof).obj f)) := by
  let := simplexModelCategory C
  have : IsCofibrant ((source cof).obj f) := ⟨source_reedyCofibrant cof f⟩
  have : Cofibration ((inclusion cof).app f) := ⟨inclusion_reedyCofibration cof f⟩
  have : IsCofibrant ((target cof).obj f) := isCofibrant_of_cofibration ((inclusion cof).app f)
  exact mem_cofibrations (initial.to ((target cof).obj f))

lemma sourceAugmentation_weakEquivalence (f : Arrow C) (n : SimplexCategory) :
    weakEquivalences C (((sourceAugmentation cof).app f).app n) :=
  ((cosimplicialResolutionFamily cof).atObject f.left).augmentation_weakEquivalence n

lemma targetAugmentation_weakEquivalence (f : Arrow C) (n : SimplexCategory) :
    weakEquivalences C (((targetAugmentation cof).app f).app n) :=
  (weakEquivalences C).comp_mem _ _ (projection_weakEquivalence cof f n)
    (((cosimplicialResolutionFamily cof).atObject f.right).augmentation_weakEquivalence n)

lemma source_homotopicallyConstant (f : Arrow C) {n m : SimplexCategory} (a : n ⟶ m) :
    weakEquivalences C (((source cof).obj f).map a) :=
  ((cosimplicialResolutionFamily cof).atObject f.left).homotopicallyConstant a

lemma target_homotopicallyConstant (f : Arrow C) {n m : SimplexCategory} (a : n ⟶ m) :
    weakEquivalences C (((target cof).obj f).map a) := by
  have hn := ((targetAugmentation cof).app f).naturality a
  have he : ((target cof).obj f).map a ≫ ((targetAugmentation cof).app f).app m =
      ((targetAugmentation cof).app f).app n := hn.trans (Category.comp_id _)
  exact (weakEquivalences C).of_postcomp _ _ (targetAugmentation_weakEquivalence cof f m)
    (he.symm ▸ targetAugmentation_weakEquivalence cof f n)

@[reassoc]
lemma over (f : Arrow C) (n : SimplexCategory) :
    ((inclusion cof).app f).app n ≫ ((targetAugmentation cof).app f).app n =
      ((sourceAugmentation cof).app f).app n ≫ f.hom := by
  let := simplexModelCategory C
  have h := congr_app ((ResolutionComparison.diagramCofFactorization cof).fac_app
    (f := (resolvedArrows cof).obj f)) n
  change ((inclusion cof).app f).app n ≫ ((projection cof).app f).app n =
    ((resolution cof).map f.hom).app n at h
  have hn : ((resolution cof).map f.hom).app n ≫
      ((cosimplicialResolutionFamily cof).augmentation.app f.right).app n =
    ((sourceAugmentation cof).app f).app n ≫ f.hom :=
      congr_app ((cosimplicialResolutionFamily cof).augmentation.naturality f.hom) n
  change ((inclusion cof).app f).app n ≫
    (((projection cof).app f).app n ≫
      ((cosimplicialResolutionFamily cof).augmentation.app f.right).app n) = _
  rw [← Category.assoc, h]
  exact hn

/-- Every degree is an actual weak square over the original arrow. -/
def degreeArrowComparison (f : Arrow C) (n : SimplexCategory) :
    Arrow.mk (((inclusion cof).app f).app n) ⟶ f :=
  Arrow.homMk (((sourceAugmentation cof).app f).app n)
    (((targetAugmentation cof).app f).app n) (over cof f n).symm

end SerrePositivity.Bousfield.ArrowFrames
