module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionUpperBound
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletionHomologyComplete
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletionReflection
public import SerrePositivity.HomologicalAlgebra.DerivedNonpositiveHom

/-! # Actual principal completion preserves H0 isomorphisms of nonpositive objects -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R)

/-- H0 of actual completion has the module reflection property on nonpositive sources. -/
def completionH0HomEquiv (X : ConcreteDerivedCategory R) [X.IsLE 0]
    (M : ModuleCat.{u} R) (hM : IsModuleComplete R a M) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj
      ((derivedComplexCompletionFunctor R a).obj X) ⟶ M) ≃
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj X ⟶ M) := by
  letI := derivedComplexCompletionFunctor_isLE R a X 0 inferInstance
  exact (derivedNonpositiveHomToSingleEquiv
    ((derivedComplexCompletionFunctor R a).obj X) M).symm |>.trans
    (derivedComplexCompletionHomEquiv R a X
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) hM) |>.trans
    (derivedNonpositiveHomToSingleEquiv X M)

@[simp] lemma completionH0HomEquiv_apply (X : ConcreteDerivedCategory R) [X.IsLE 0]
    (M : ModuleCat.{u} R) (hM : IsModuleComplete R a M)
    (g : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj
      ((derivedComplexCompletionFunctor R a).obj X) ⟶ M) :
    completionH0HomEquiv R a X M hM g =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map
        ((derivedComplexCompletionUnit R a).app X) ≫ g := by
  let := derivedComplexCompletionFunctor_isLE R a X 0 inferInstance
  simp only [completionH0HomEquiv, Equiv.trans_apply,
    derivedComplexCompletionHomEquiv_apply, derivedNonpositiveHomToSingleEquiv_precomp,
    Equiv.apply_symm_apply]

lemma completionH0HomEquiv_precomp {X Y : ConcreteDerivedCategory R} [X.IsLE 0] [Y.IsLE 0]
    (M : ModuleCat.{u} R) (hM : IsModuleComplete R a M) (f : X ⟶ Y)
    (g : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj
      ((derivedComplexCompletionFunctor R a).obj Y) ⟶ M) :
    completionH0HomEquiv R a X M hM
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map
        ((derivedComplexCompletionFunctor R a).map f) ≫ g) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map f ≫
        completionH0HomEquiv R a Y M hM g := by
  rw [completionH0HomEquiv_apply, completionH0HomEquiv_apply]
  have hn := congrArg (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map
    ((derivedComplexCompletionUnit R a).naturality f)
  simp only [Functor.map_comp, Functor.id_map] at hn
  rw [← Category.assoc, ← hn, Category.assoc]

/-- G11-2 on the original unbounded derived category, for the original morphism f. -/
theorem derivedComplexCompletion_h0_map_isIso {X Y : ConcreteDerivedCategory R} (f : X ⟶ Y)
    (hX : X.IsLE 0) (hY : Y.IsLE 0)
    (hf : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map f)) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map
      ((derivedComplexCompletionFunctor R a).map f)) := by
  let := hX
  let := hY
  let := hf
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0
  let L := derivedComplexCompletionFunctor R a
  have hpre (M : ModuleCat.{u} R) (hM : IsModuleComplete R a M) :
      Function.Bijective (fun g : H.obj (L.obj Y) ⟶ M ↦ H.map (L.map f) ≫ g) := by
    let E := ((completionH0HomEquiv R a Y M hM).trans
      (Iso.homCongr (asIso (H.map f)).symm (Iso.refl M))).trans
      (completionH0HomEquiv R a X M hM).symm
    have he (g : H.obj (L.obj Y) ⟶ M) : E g = H.map (L.map f) ≫ g := by
      apply (completionH0HomEquiv R a X M hM).injective
      simp only [E, Equiv.trans_apply,
        Iso.homCongr_apply, Iso.symm_inv, Iso.refl_hom, Category.comp_id]
      erw [Equiv.apply_symm_apply]
      exact (completionH0HomEquiv_precomp R a M hM f g).symm
    have hfun : (E : _ → _) = (fun g ↦ H.map (L.map f) ≫ g) := funext he
    rw [← hfun]
    exact E.bijective
  obtain ⟨g, hg⟩ := (hpre (H.obj (L.obj X))
    (derivedComplexCompletionFunctor_homology_isModuleComplete R a X 0)).2 (𝟙 _)
  have hi := (hpre (H.obj (L.obj Y))
    (derivedComplexCompletionFunctor_homology_isModuleComplete R a Y 0)).1
  have hgf : g ≫ H.map (L.map f) = 𝟙 _ := by
    apply hi
    change H.map (L.map f) ≫ (g ≫ H.map (L.map f)) = H.map (L.map f) ≫ 𝟙 _
    change H.map (L.map f) ≫ g = 𝟙 _ at hg
    rw [← Category.assoc, hg, Category.id_comp, Category.comp_id]
  exact ⟨⟨g, hg, hgf⟩⟩

/-- Exact G11 request for the existing bounded-above functor and the given morphism. -/
theorem boundedAboveDerivedCompletion_h0_map_isIso
    {X Y : DerivedCategory.Minus (ModuleCat.{u} R)} (f : X ⟶ Y)
    (hX : X.obj.IsLE 0) (hY : Y.obj.IsLE 0)
    (hf : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map f.hom)) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map
      (((boundedAboveDerivedCompletionFunctor R a).map f).hom)) :=
  derivedComplexCompletion_h0_map_isIso R a f.hom hX hY hf

end SerrePositivity.DerivedCompletion
