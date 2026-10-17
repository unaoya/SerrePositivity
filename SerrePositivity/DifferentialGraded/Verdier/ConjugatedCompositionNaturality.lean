module
public import SerrePositivity.DifferentialGraded.Verdier.KernelCompositionNaturality

/-! # 完備商・局所 perfect へ運んだ合成比較の自然性 -/
@[expose] public section
noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor Idempotents Morita

section General
variable {C₀ C₁ C₂ V₀ V₁ V₂ : Type*}
  [Category* C₀] [Category* C₁] [Category* C₂]
  [Category* V₀] [Category* V₁] [Category* V₂]
  (e₀ : C₀ ≌ V₀) (e₁ : C₁ ≌ V₁) (e₂ : C₂ ≌ V₂)
  {P P' : V₀ ⥤ V₁} {Q Q' : V₁ ⥤ V₂} {R R' : V₀ ⥤ V₂}
  (α : P ⟶ P') (β : Q ⟶ Q') (γ : R ⟶ R') (e : P ⋙ Q ≅ R) (e' : P' ⋙ Q' ≅ R')

/-- 比較同値で運んだ合成同型は、元の合成同型の自然性を保つ。 -/
lemma conjugatedKernelCompositionIso_naturality
    (he : NatTrans.hcomp α β ≫ e'.hom = e.hom ≫ γ) :
    NatTrans.hcomp (whiskerLeft e₀.functor (whiskerRight α e₁.inverse))
        (whiskerLeft e₁.functor (whiskerRight β e₂.inverse)) ≫
        (conjugatedKernelCompositionIso e₀ e₁ e₂ P' Q' R' e').hom =
      (conjugatedKernelCompositionIso e₀ e₁ e₂ P Q R e).hom ≫
        whiskerLeft e₀.functor (whiskerRight γ e₂.inverse) := by
  apply NatTrans.ext
  funext X
  have hc := e₁.counitIso.hom.naturality (α.app (e₀.functor.obj X))
  simp only [Functor.comp_map, Functor.id_map] at hc
  have hb := β.naturality (e₁.counitIso.hom.app (P.obj (e₀.functor.obj X)))
  have hh := NatTrans.congr_app he (e₀.functor.obj X)
  simp only [NatTrans.comp_app, NatTrans.hcomp_app, Category.assoc] at hh
  simp only [conjugatedKernelCompositionIso, Iso.trans_hom, Iso.symm_hom,
    isoWhiskerRight_hom, isoWhiskerLeft_hom, NatTrans.comp_app,
    whiskerRight_app, whiskerLeft_app, associator_inv_app, associator_hom_app,
    leftUnitor_hom_app, NatTrans.hcomp_app, Functor.comp_map, Functor.comp_obj,
    Functor.id_obj, Category.id_comp, Category.assoc]
  simp only [← CategoryTheory.Functor.map_comp]
  apply congrArg e₂.inverse.map
  rw [← Q'.map_comp_assoc, hc, Q'.map_comp, Category.assoc,
    ← reassoc_of% hb, hh]
end General

namespace DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (B : Type z) [DGCategory A B] [Small.{u} B]
  (S : Set D) (T : Set E) (U : Set B) (hD : localHomKFlat A D)
  (P P' : SupportedPerfectKernelCategory A D E S T)
  (Q Q' : SupportedPerfectKernelCategory A E B T U) (f : P ⟶ P') (g : Q ⟶ Q')

lemma supportedKernelCompletedTriaCompositionIso_naturality :
    NatTrans.hcomp ((supportedKernelCompletedTriaFunctor A D S E T).map f)
        ((supportedKernelCompletedTriaFunctor A E T B U).map g) ≫
        (supportedKernelCompletedTriaCompositionIso A D E B S T U hD P' Q').hom =
      (supportedKernelCompletedTriaCompositionIso A D E B S T U hD P Q).hom ≫
        (supportedKernelCompletedTriaFunctor A D S B U).map
          (supportedKernelCompositionMap A D E B S T U hD P P' Q Q' f g) :=
  conjugatedKernelCompositionIso_naturality
    (perfectCompletedToTriaQuotientEquivalence A D S).symm
    (perfectCompletedToTriaQuotientEquivalence A E T).symm
    (perfectCompletedToTriaQuotientEquivalence A B U).symm _ _ _ _ _
    (supportedKernelCompletedCompositionIso_naturality A D E B S T U hD P P' Q Q' f g)

variable (hS : localKFlat A D S) (hT : localKFlat A E T) (hU : localKFlat A B U)

lemma supportedKernelLocalPerfectCompositionIso_naturality :
    NatTrans.hcomp ((supportedKernelLocalPerfectFunctor A D S E T hS hT).map f)
        ((supportedKernelLocalPerfectFunctor A E T B U hT hU).map g) ≫
        (supportedKernelLocalPerfectCompositionIso A D E B S T U hD P' Q' hS hT hU).hom =
      (supportedKernelLocalPerfectCompositionIso A D E B S T U hD P Q hS hT hU).hom ≫
        (supportedKernelLocalPerfectFunctor A D S B U hS hU).map
          (supportedKernelCompositionMap A D E B S T U hD P P' Q Q' f g) :=
  conjugatedKernelCompositionIso_naturality
    (localPerfectToPerfectVerdierEquivalence A D S hS)
    (localPerfectToPerfectVerdierEquivalence A E T hT)
    (localPerfectToPerfectVerdierEquivalence A B U hU) _ _ _ _ _
    (supportedKernelCompletedCompositionIso_naturality A D E B S T U hD P P' Q Q' f g)
end DGQuotient
end SerrePositivity.DifferentialGraded
