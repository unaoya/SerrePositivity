module

public import SerrePositivity.HomotopicalAlgebra.Smith.AccessibleSquares
public import SerrePositivity.HomotopicalAlgebra.Smith.AccessibleFactorization
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-! # Accessibility of Mathlib's actual cell-attachment successor

The pushout is formed in the functor category, using the two square-indexed
coproduct functors. Accessibility of this pushout follows from accessibility
of its three vertices. No accessibility assumption on the successor is used.
-/

@[expose] public section
universe w u
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.Smith.AccessibleCellAttachment
variable {C : Type u} [Category.{w} C] [HasColimitsOfSize.{w, w} C]
  {ι : Type w} (a : ι → Arrow C)

abbrev source := AccessibleSquares.rawCells a (fun i ↦ (a i).left)
abbrev target := AccessibleSquares.rawCells a (fun i ↦ (a i).right)
abbrev step := SmallObject.functor (fun i ↦ (a i).hom)
abbrev stepObject : Arrow C ⥤ C := step a ⋙ Arrow.leftFunc

def top : source a ⟶ Arrow.leftFunc where
  app f := SmallObject.functorObjTop (fun i ↦ (a i).hom) f.hom
  naturality _f _g φ := SmallObject.functorMapSrc_functorObjTop (fun i ↦ (a i).hom) φ

def boundary : source a ⟶ target a where
  app f := SmallObject.functorObjLeft (fun i ↦ (a i).hom) f.hom
  naturality _f _g φ := (SmallObject.functorMap_comm (fun i ↦ (a i).hom) φ).symm

def inclusion : Arrow.leftFunc ⟶ stepObject a where
  app f := SmallObject.ιFunctorObj (fun i ↦ (a i).hom) f.hom
  naturality _f _g φ := (SmallObject.ιFunctorObj_naturality (fun i ↦ (a i).hom) φ).symm

def cellInclusion : target a ⟶ stepObject a where
  app f := SmallObject.ρFunctorObj (fun i ↦ (a i).hom) f.hom
  naturality f g φ := by
    change SmallObject.functorMapTgt (fun i ↦ (a i).hom) φ ≫
        SmallObject.ρFunctorObj (fun i ↦ (a i).hom) g.hom =
      SmallObject.ρFunctorObj (fun i ↦ (a i).hom) f.hom ≫
        SmallObject.functorMap (fun i ↦ (a i).hom) φ
    simp [SmallObject.ρFunctorObj, SmallObject.functorMap]

def cocone : PushoutCocone (top a) (boundary a) :=
  PushoutCocone.mk (inclusion a) (cellInclusion a) (by
    apply NatTrans.ext
    funext f
    exact SmallObject.functorObj_comm (fun i ↦ (a i).hom) f.hom)

def isColimitCocone : IsColimit (cocone a) :=
  evaluationJointlyReflectsColimits _ (fun f ↦ by
    exact (PushoutCocone.isColimitMapCoconeEquiv (cocone a)
      ((evaluation (Arrow C) C).obj f)).symm
        (SmallObject.functorObj_isPushout (fun i ↦ (a i).hom) f.hom).isColimit)

lemma stepObject_isCardinalAccessible (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [∀ i, IsCardinalPresentable (a i).left κ]
    [∀ i, IsCardinalPresentable (a i).right κ] : (stepObject a).IsCardinalAccessible κ := by
  have : (source a).IsCardinalAccessible κ :=
    AccessibleSquares.rawCells_isCardinalAccessible a _ κ
  have : (target a).IsCardinalAccessible κ :=
    AccessibleSquares.rawCells_isCardinalAccessible a _ κ
  have : (Arrow.leftFunc : Arrow C ⥤ C).IsCardinalAccessible κ :=
    AccessibleFactorization.arrow_left_isCardinalAccessible κ
  have : ∀ k, ((span (top a) (boundary a)).obj k).IsCardinalAccessible κ := by
    intro k
    cases k with
    | none => exact inferInstanceAs ((source a).IsCardinalAccessible κ)
    | some k => cases k <;> assumption
  have : (colimit.cocone (span (top a) (boundary a))).pt.IsCardinalAccessible κ :=
    AccessibleColimits.colimit_isCardinalAccessible _ κ
  exact Functor.isCardinalAccessible_of_natIso
    ((colimit.isColimit _).coconePointUniqueUpToIso (isColimitCocone a)) κ

lemma step_isCardinalAccessible (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [∀ i, IsCardinalPresentable (a i).left κ]
    [∀ i, IsCardinalPresentable (a i).right κ] : (step a).IsCardinalAccessible κ := by
  have := AccessibleFactorization.arrow_right_isCardinalAccessible (C := C) κ
  have : (step a ⋙ Arrow.leftFunc).IsCardinalAccessible κ := stepObject_isCardinalAccessible a κ
  have : (step a ⋙ Arrow.rightFunc).IsCardinalAccessible κ :=
    inferInstanceAs ((Arrow.rightFunc : Arrow C ⥤ C).IsCardinalAccessible κ)
  exact AccessibleFactorization.arrowFunctor_isCardinalAccessible _ κ

end SerrePositivity.Smith.AccessibleCellAttachment
