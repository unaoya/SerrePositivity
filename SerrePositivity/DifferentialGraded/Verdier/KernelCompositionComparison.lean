module
public import SerrePositivity.DifferentialGraded.Verdier.KernelCompositionDescent

/-! # kernel 合成と完備 tria 商・局所 perfect enhancement の比較 -/
@[expose] public section
noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor Idempotents Morita

/-- 固定した比較同値による作用の輸送は、元の作用の合成同型を保つ。 -/
def conjugatedKernelCompositionIso
    {C₀ C₁ C₂ V₀ V₁ V₂ : Type*}
    [Category* C₀] [Category* C₁] [Category* C₂]
    [Category* V₀] [Category* V₁] [Category* V₂]
    (e₀ : C₀ ≌ V₀) (e₁ : C₁ ≌ V₁) (e₂ : C₂ ≌ V₂)
    (P : V₀ ⥤ V₁) (Q : V₁ ⥤ V₂) (R : V₀ ⥤ V₂) (α : P ⋙ Q ≅ R) :
    (e₀.functor ⋙ P ⋙ e₁.inverse) ⋙ (e₁.functor ⋙ Q ⋙ e₂.inverse) ≅
      e₀.functor ⋙ R ⋙ e₂.inverse := by
  let β : e₁.inverse ⋙ (e₁.functor ⋙ (Q ⋙ e₂.inverse)) ≅ Q ⋙ e₂.inverse :=
    (associator _ _ _).symm ≪≫ isoWhiskerRight e₁.counitIso _ ≪≫ leftUnitor _
  exact associator _ _ _ ≪≫
    isoWhiskerLeft e₀.functor (associator _ _ _) ≪≫
    isoWhiskerLeft e₀.functor (isoWhiskerLeft P β) ≪≫
    isoWhiskerLeft e₀.functor (associator P Q e₂.inverse).symm ≪≫
    isoWhiskerLeft e₀.functor (isoWhiskerRight α e₂.inverse)

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (B : Type z) [DGCategory A B] [Small.{u} B]
  (S : Set D) (T : Set E) (U : Set B) (hD : localHomKFlat A D)
  (P : SupportedPerfectKernelCategory A D E S T)
  (Q : SupportedPerfectKernelCategory A E B T U)

namespace DGQuotient

/-- 完備 tria 商の実際の誘導作用にも、元の kernel 合成同型が降りる。 -/
def supportedKernelCompletedTriaCompositionIso :
    (supportedKernelCompletedTriaFunctor A D S E T).obj P ⋙
        (supportedKernelCompletedTriaFunctor A E T B U).obj Q ≅
      (supportedKernelCompletedTriaFunctor A D S B U).obj
        (supportedKernelComposite A D E B S T U hD P Q) :=
  conjugatedKernelCompositionIso
    (perfectCompletedToTriaQuotientEquivalence A D S).symm
    (perfectCompletedToTriaQuotientEquivalence A E T).symm
    (perfectCompletedToTriaQuotientEquivalence A B U).symm _ _ _
    (supportedKernelCompletedCompositionIso A D E B S T U hD P Q)

variable (hS : localKFlat A D S) (hT : localKFlat A E T) (hU : localKFlat A B U)

/-- 局所 perfect enhancement の H⁰ 作用の合成比較。局所条件は三つの商ごとに明示する。 -/
def supportedKernelLocalPerfectCompositionIso :
    (supportedKernelLocalPerfectFunctor A D S E T hS hT).obj P ⋙
        (supportedKernelLocalPerfectFunctor A E T B U hT hU).obj Q ≅
      (supportedKernelLocalPerfectFunctor A D S B U hS hU).obj
        (supportedKernelComposite A D E B S T U hD P Q) :=
  conjugatedKernelCompositionIso
    (localPerfectToPerfectVerdierEquivalence A D S hS)
    (localPerfectToPerfectVerdierEquivalence A E T hT)
    (localPerfectToPerfectVerdierEquivalence A B U hU) _ _ _
    (supportedKernelCompletedCompositionIso A D E B S T U hD P Q)
end DGQuotient
end SerrePositivity.DifferentialGraded
