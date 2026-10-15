module

public import Mathlib.CategoryTheory.Presentable.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Pointwise colimits of accessible functors

The cardinal is fixed throughout. These lemmas will be used at the colimit
stages of an accessible small-object construction; functoriality of that
construction by itself is not used as an accessibility hypothesis.
-/

@[expose] public section
universe w v u v' u' t s
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.Smith.AccessibleColimits
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {K : Type t} [Category.{s} K]

/-- Evaluation detects preservation of cardinal-filtered colimits. -/
lemma functorCategory_isCardinalAccessible (F : D ⥤ K ⥤ C)
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [∀ k, (F ⋙ (evaluation K C).obj k).IsCardinalAccessible κ] :
    F.IsCardinalAccessible κ where
  preservesColimitOfShape J _ _ := by
    have := fun k ↦ Functor.preservesColimitsOfShape_of_isCardinalAccessible
      (F ⋙ (evaluation K C).obj k) κ J
    exact { preservesColimit := { preserves hc := ⟨
      evaluationJointlyReflectsColimits _ (fun k ↦
        isColimitOfPreserves (F ⋙ (evaluation K C).obj k) hc)⟩ } }

/-- Compute a colimit of functors pointwise, keeping the diagram explicit. -/
def pointwiseColimit [HasColimitsOfShape K C] (F : K ⥤ D ⥤ C) : D ⥤ C :=
  F.flip ⋙ colim

lemma pointwiseColimit_isCardinalAccessible [HasColimitsOfShape K C]
    (F : K ⥤ D ⥤ C) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [∀ k, (F.obj k).IsCardinalAccessible κ] :
    (pointwiseColimit F).IsCardinalAccessible κ := by
  have : ∀ k, (F.flip ⋙ (evaluation K C).obj k).IsCardinalAccessible κ :=
    fun k ↦ inferInstanceAs ((F.obj k).IsCardinalAccessible κ)
  have := functorCategory_isCardinalAccessible F.flip κ
  exact inferInstanceAs ((F.flip ⋙ colim).IsCardinalAccessible κ)

/-- The ordinary chosen colimit functor has the same property. -/
lemma colimit_isCardinalAccessible [HasColimitsOfShape K C]
    (F : K ⥤ D ⥤ C) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [∀ k, (F.obj k).IsCardinalAccessible κ] :
    (colimit F).IsCardinalAccessible κ := by
  have : (F.flip ⋙ colim).IsCardinalAccessible κ :=
    pointwiseColimit_isCardinalAccessible F κ
  exact Functor.isCardinalAccessible_of_natIso (colimitIsoFlipCompColim F).symm κ

end SerrePositivity.Smith.AccessibleColimits
