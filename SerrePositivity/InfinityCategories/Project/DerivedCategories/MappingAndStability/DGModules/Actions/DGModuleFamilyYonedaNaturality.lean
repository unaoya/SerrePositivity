module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleFamilyYoneda
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleSubcategoryYonedaCone
/-!
概要：ラベル評価後の制限 Yoneda と、元のラベル圏の Yoneda の自然同型を構成する。
方針：同じ Hom 複体への対象比較を、実評価の閉射比較へ接続する。
規約：対象の単射性やラベルの消去を要求しない。
使われ方：c′ の零・shift・cone のホモトピー表現可能性を b の一般判定へ渡す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (I : Type w) [Small.{u} I] (value : I → RightModule R D)

def dgModuleFamilyYonedaClosedIso :
    letI := inducedDGCategory R value
    ((inducedDGEvaluation R value).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFamilyYoneda R D I value)).onClosed ≅
      (dgYoneda R I).onClosed := by
  letI := inducedDGCategory R value
  refine NatIso.ofComponents (fun X => eqToIso (congrArg
    (ForgetEnrichment.of (Complex R))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFamilyYoneda_obj R D I value (ForgetEnrichment.to (Complex R) X)))) ?_
  intro X Y f
  apply moduleMorphism_ext R I
  intro T
  simp only [eqToIso.hom, eqToHom_refl, Category.comp_id, Category.id_comp]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaEvaluation_closed_map]
  change (closedToComplex R).map (ForgetEnrichment.homOf (Complex R)
    ((ForgetEnrichment.homTo (Complex R) f ≫ (𝟙 _ ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorRestrictedYoneda R I (RightModule R D)
        (inducedDGEvaluation R value)).toFunctor.map
        (value (ForgetEnrichment.to (Complex R) X))
        (value (ForgetEnrichment.to (Complex R) Y)))) ≫
      moduleHomπ R I _ _ T)) = _
  rw [Category.id_comp, Category.assoc]
  erw [Bimodule.ofParamTrans_map_π]
  change (closedToComplex R).map (ForgetEnrichment.homOf (Complex R)
    (ForgetEnrichment.homTo (Complex R) f ≫
      yonedaExtensionApp R (value (ForgetEnrichment.to (Complex R) X))
        (representable R (value (ForgetEnrichment.to (Complex R) Y))) (𝟙 _)
        (Opposite.op (value T)))) = _
  rw [endomorphismYonedaApp]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
