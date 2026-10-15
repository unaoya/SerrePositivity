module

public import Mathlib.CategoryTheory.Presentable.Basic
public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-! # Presentability reflected by an accessible fully faithful functor -/

@[expose] public section
universe w v₁ v₂ u₁ u₂
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.Smith

lemma presentable_of_accessible_fullyFaithful
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) [F.Full] [F.Faithful] (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [F.IsCardinalAccessible κ] (X : C) [IsCardinalPresentable (F.obj X) κ] :
    IsCardinalPresentable X κ := by
  apply IsCardinalPresentable.mk
  intro J _ _ G c hc
  have := F.preservesColimitsOfShape_of_isCardinalAccessible κ J
  have hFc := isColimitOfPreserves F hc
  constructor
  · intro g
    obtain ⟨j, f, hf⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ hFc (F.map g)
    refine ⟨j, F.preimage f, F.map_injective ?_⟩
    change f ≫ F.map (c.ι.app j) = F.map g at hf
    simpa only [Functor.map_comp, Functor.map_preimage] using hf
  · intro j f₁ f₂ h
    obtain ⟨j', a, ha⟩ := IsCardinalPresentable.exists_eq_of_isColimit'
      κ hFc (F.map f₁) (F.map f₂) (by
        change F.map f₁ ≫ F.map (c.ι.app j) = F.map f₂ ≫ F.map (c.ι.app j)
        simpa only [← Functor.map_comp] using congrArg (fun f ↦ F.map f) h)
    refine ⟨j', a, F.map_injective ?_⟩
    change F.map f₁ ≫ F.map (G.map a) = F.map f₂ ≫ F.map (G.map a) at ha
    simpa only [Functor.map_comp] using ha

end SerrePositivity.Smith
