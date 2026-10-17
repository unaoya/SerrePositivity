module
public import SerrePositivity.DifferentialGraded.Module.FunctorExtensionUnit
public import SerrePositivity.DifferentialGraded.Module.FunctorExtensionMaps

/-! # graph延長–制限の単位の加群変数に関する自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

lemma functorExtensionInsertion_map {M N : ModuleCategory A D} (f : M ⟶ N) (d : D) :
    (moduleEvaluation A D d).map f ≫ functorExtensionInsertionComponent A D E F
        (ForgetEnrichment.to (Complex A) N) d =
      functorExtensionInsertionComponent A D E F (ForgetEnrichment.to (Complex A) M) d ≫
        (moduleEvaluation A E (F.obj d)).map ((dgModuleExtension A D E F).onClosed.map f) := by
  rw [dgModuleExtension_map_eval]
  apply chain_ext_apply
  intro r m
  change (functorExtensionInsertionComponent A D E F
    (ForgetEnrichment.to (Complex A) N) d).f r
      (((moduleEvaluation A D d).map f).f r m) =
    (BalancedTensor.rightTensorMap A D ((functorGraph A D E F).leftAt (F.obj d)) f).f r
      ((functorExtensionInsertionComponent A D E F
        (ForgetEnrichment.to (Complex A) M) d).f r m)
  rw [functorExtensionInsertion_apply, functorExtensionInsertion_apply]
  exact (BalancedTensor.rightTensorMap_element A D
    ((functorGraph A D E F).leftAt (F.obj d)) f d m
      (unitElement A (F.obj d)).val (add_zero r)).symm

/-- 通常dg加群圏の延長–制限に対する自然な単位。 -/
def dgModuleUnit : 𝟭 (ModuleCategory A D) ⟶
    (dgModuleExtension A D E F).onClosed ⋙ moduleRestriction A D E F.op where
  app M := functorExtensionUnit A D E F (ForgetEnrichment.to (Complex A) M)
  naturality {M N} f := by
    apply moduleMorphism_ext
    intro d
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      functorExtensionUnit_eval, functorExtensionUnit_eval]
    simp only [CategoryTheory.Functor.id_map, CategoryTheory.Functor.comp_map]
    rw [moduleRestriction_map_eval]
    exact functorExtensionInsertion_map A D E F f d

end SerrePositivity.DifferentialGraded
