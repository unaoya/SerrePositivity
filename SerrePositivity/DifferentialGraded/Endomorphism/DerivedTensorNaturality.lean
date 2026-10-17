module
public import SerrePositivity.DifferentialGraded.Endomorphism.DerivedTensor

/-! # 解像度による再構成導来tensor計算の自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D)

lemma endomorphismResolutionDerivedTensorComputation_naturality
    (R : ∀ N : ModuleCategory A (EndomorphismObject E),
      ModuleProjectiveResolution A (EndomorphismObject E) N)
    {N N' : ModuleCategory A (EndomorphismObject E)} (f : N ⟶ N') :
    (endomorphismResolutionDerivedTensor A D E R).map
        ((moduleToDerived A (EndomorphismObject E)).map f) ≫
        (endomorphismResolutionDerivedTensorComputation A D E R N').hom =
      (endomorphismResolutionDerivedTensorComputation A D E R N).hom ≫
        (moduleToDerived A D).map
          ((endomorphismModuleTensor A D E).onClosed.map ((R N).lift (R N') f)) := by
  let H := (endomorphismModuleTensor A D E).onHomotopy ⋙ moduleHomotopyToDerivedClosed A D
  have h₁ := congrArg H.map
    ((moduleDerivedResolutionFunctor_fac A (EndomorphismObject E) R).hom.naturality f)
  simp only [Functor.map_comp] at h₁
  have h₂ := congrArg (moduleHomotopyToDerivedClosed A D).map
    ((eqToIso (endomorphismModuleTensor A D E).onHomotopy_fac).hom.naturality
      ((R N).lift (R N') f))
  simp only [Functor.map_comp] at h₂
  have h₃ := (moduleToHomotopyDerivedIso A D).hom.naturality
    ((endomorphismModuleTensor A D E).onClosed.map ((R N).lift (R N') f))
  change H.map ((moduleDerivedResolutionFunctor A (EndomorphismObject E) R).map
      ((moduleToDerived A (EndomorphismObject E)).map f)) ≫
      H.map (moduleDerivedResolutionComputation A (EndomorphismObject E) R N').hom =
    H.map (moduleDerivedResolutionComputation A (EndomorphismObject E) R N).hom ≫
      H.map ((moduleToHomotopy A (EndomorphismObject E)).map ((R N).lift (R N') f)) at h₁
  change H.map ((moduleToHomotopy A (EndomorphismObject E)).map ((R N).lift (R N') f)) ≫
      (moduleHomotopyToDerivedClosed A D).map
        (endomorphismTensorHomotopyComputation A D E (R N').obj).hom =
    (moduleHomotopyToDerivedClosed A D).map
        (endomorphismTensorHomotopyComputation A D E (R N).obj).hom ≫
      (moduleHomotopyToDerivedClosed A D).map
        ((moduleToHomotopy A D).map
          ((endomorphismModuleTensor A D E).onClosed.map ((R N).lift (R N') f))) at h₂
  change (moduleHomotopyToDerivedClosed A D).map
      ((moduleToHomotopy A D).map
        ((endomorphismModuleTensor A D E).onClosed.map ((R N).lift (R N') f))) ≫
      ((moduleToHomotopyDerivedIso A D).app
        ((endomorphismModuleTensor A D E).onClosed.obj (R N').obj)).hom =
    ((moduleToHomotopyDerivedIso A D).app
        ((endomorphismModuleTensor A D E).onClosed.obj (R N).obj)).hom ≫
      (moduleToDerived A D).map
        ((endomorphismModuleTensor A D E).onClosed.map ((R N).lift (R N') f)) at h₃
  change H.map _ ≫ (H.map _ ≫ _ ≫ _) = (H.map _ ≫ _ ≫ _) ≫ _
  rw [← Category.assoc, h₁]
  simp only [Category.assoc]
  apply congrArg (fun t => H.map
    (moduleDerivedResolutionComputation A (EndomorphismObject E) R N).hom ≫ t)
  have h₄ := congrArg
    (fun t => t ≫ (moduleToHomotopyDerivedIso A D).hom.app
      ((endomorphismModuleTensor A D E).onClosed.obj (R N').obj)) h₂
  have h₅ := congrArg
    (fun t => (moduleHomotopyToDerivedClosed A D).map
      (endomorphismTensorHomotopyComputation A D E (R N).obj).hom ≫ t) h₃
  simp only [Category.assoc] at h₄ h₅
  have h₆ := h₄.trans h₅
  exact h₆

lemma endomorphismDerivedTensorResolutionComputation_canonical
    (N : ModuleCategory A (EndomorphismObject E)) :
    endomorphismDerivedTensorResolutionComputation A D E
        (moduleCanonicalProjectiveResolution A (EndomorphismObject E) N) =
      endomorphismResolutionDerivedTensorComputation A D E
        (moduleCanonicalProjectiveResolution A (EndomorphismObject E)) N := by
  simp [endomorphismDerivedTensorResolutionComputation,
    endomorphismProjectiveResolutionTensorIso_self]

lemma endomorphismDerivedTensorResolutionComputation_inv_naturality
    {N N' : ModuleCategory A (EndomorphismObject E)} (f : N ⟶ N') :
    (endomorphismDerivedTensorResolutionComputation A D E
        (moduleCanonicalProjectiveResolution A (EndomorphismObject E) N)).inv ≫
        (endomorphismDerivedTensor A D E).map
          ((moduleToDerived A (EndomorphismObject E)).map f) =
      (moduleToDerived A D).map ((endomorphismModuleTensor A D E).onClosed.map
        ((moduleCanonicalProjectiveResolution A (EndomorphismObject E) N).lift
          (moduleCanonicalProjectiveResolution A (EndomorphismObject E) N') f)) ≫
        (endomorphismDerivedTensorResolutionComputation A D E
          (moduleCanonicalProjectiveResolution A (EndomorphismObject E) N')).inv := by
  rw [endomorphismDerivedTensorResolutionComputation_canonical,
    endomorphismDerivedTensorResolutionComputation_canonical]
  dsimp only [endomorphismDerivedTensor]
  have h := endomorphismResolutionDerivedTensorComputation_naturality A D E
    (moduleCanonicalProjectiveResolution A (EndomorphismObject E)) f
  apply (cancel_mono (endomorphismResolutionDerivedTensorComputation A D E
    (moduleCanonicalProjectiveResolution A (EndomorphismObject E)) N').hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h, Iso.inv_hom_id_assoc]

end SerrePositivity.DifferentialGraded
