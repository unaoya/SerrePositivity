module
public import SerrePositivity.DifferentialGraded.Module.FunctorExtensionUnit
public import SerrePositivity.DifferentialGraded.Module.RestrictionRepresentable

/-! # 代表加群上での延長–制限単位とdg関手のHom比較の一致 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

lemma functorExtensionUnit_representable (d : D) :
    functorExtensionUnit A D E F (representable A d) ≫
      (moduleRestriction A D E F.op).map (dgModuleExtensionRepresentableIso A D E F d).hom =
        representableRestrictionMap A D E F d := by
  apply moduleMorphism_ext
  intro x
  rw [CategoryTheory.Functor.map_comp, functorExtensionUnit_eval,
    moduleRestriction_map_eval, representableRestrictionMap_eval]
  change functorExtensionInsertionComponent A D E F (representable A d) x ≫
    (moduleEvaluation A E (F.obj x)).map
      (BimoduleTensor.rightUnitIso A E D (functorGraph A D E F) d).hom = F.map x d
  rw [BimoduleTensor.rightUnitIso_hom_eval]
  change functorExtensionInsertionComponent A D E F (representable A d) x ≫
    BalancedTensor.yonedaEvaluation A D d ((functorGraph A D E F).leftAt (F.obj x)) = _
  apply chain_ext_apply
  intro r f
  change (BalancedTensor.yonedaEvaluation A D d
    ((functorGraph A D E F).leftAt (F.obj x))).f r
      ((functorExtensionInsertionComponent A D E F (representable A d) x).f r f) =
    (F.map x d).f r f
  rw [functorExtensionInsertion_apply, BalancedTensor.yonedaEvaluation_element]
  exact functorGraph_leftAction_unit A D E F x d f

lemma functorExtensionUnit_representable_quasiIso (hF : HomQuasiIso F) (d : D) :
    moduleQuasiIso A D (functorExtensionUnit A D E F (representable A d)) := by
  have hg : moduleQuasiIso A D ((moduleRestriction A D E F.op).map
      (dgModuleExtensionRepresentableIso A D E F d).hom) := fun x => by infer_instance
  have hfg : moduleQuasiIso A D (functorExtensionUnit A D E F (representable A d) ≫
      (moduleRestriction A D E F.op).map (dgModuleExtensionRepresentableIso A D E F d).hom) := by
    rw [functorExtensionUnit_representable]
    exact representableRestrictionMap_quasiIso A D E F hF d
  exact (moduleQuasiIso A D).of_postcomp _ _ hg hfg

end SerrePositivity.DifferentialGraded
