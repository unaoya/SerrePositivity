module
public import SerrePositivity.DifferentialGraded.Module.Restriction
public import SerrePositivity.DifferentialGraded.Module.TensorSource
public import SerrePositivity.DifferentialGraded.Complexes.AssociatorCochainNaturality

/-! # 制限とtensor、およびtensor加群の括弧変更 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

def tensorModuleAssociatorIso [Small.{u} D] (K L : Complex A) (M : RightModule A D) :
    ForgetEnrichment.of (Complex A) (tensorModule K (tensorModule L M)) ≅
      ForgetEnrichment.of (Complex A) (tensorModule (K ⊗ L) M) :=
  moduleIsoMk A D (M := tensorModule K (tensorModule L M)) (N := tensorModule (K ⊗ L) M)
    (fun x => (α_ K L (M.obj x)).symm) (by
      intro x y
      apply hom_naturality_of_apply
      intro p f
      exact associator_inv_cochain_right K L (M.obj x) (M.obj y) p ((M.map x y).f p f))

variable (E : Type w) [DGCategory A E]

lemma restrictModule_tensor (F : DGFunctor A Dᵒᵖ Eᵒᵖ) (K : Complex A) (M : RightModule A E) :
    restrictModule A D E F (tensorModule K M) = tensorModule K (restrictModule A D E F M) := by
  apply EnrichedFunctor.ext (Complex A)
    (F := (restrictModule A D E F (tensorModule K M)).toFunctor)
    (G := (tensorModule K (restrictModule A D E F M)).toFunctor) (fun _ => rfl)
  intro x y
  change (F.map x y ≫ (M.map (F.obj x) (F.obj y) ≫ tensorLeftHom K _ _)) ≫ 𝟙 _ =
    (F.map x y ≫ M.map (F.obj x) (F.obj y)) ≫ tensorLeftHom K _ _
  rw [Category.comp_id, Category.assoc]

def moduleRestrictionTensorIso [Small.{u} D] [Small.{u} E]
    (F : DGFunctor A Dᵒᵖ Eᵒᵖ) (K : Complex A) (M : ModuleCategory A E) :
    (moduleRestriction A D E F).obj (moduleTensorLeftObj A E K M) ≅
      moduleTensorLeftObj A D K ((moduleRestriction A D E F).obj M) :=
  eqToIso (congrArg (ForgetEnrichment.of (Complex A))
    (restrictModule_tensor A D E F K (ForgetEnrichment.to (Complex A) M)))

end SerrePositivity.DifferentialGraded
