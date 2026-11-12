module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UnitCochainElement
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison

/-! 単位に作用させた全 Hom 円錐左包含は、指定した実加群円錐の左包含元そのもの。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  {P Q : ModuleCategory R C} (f : P ⟶ Q)
local notation "U" => ForgetEnrichment.to (Complex R) P
local notation "K" => ForgetEnrichment.to (Complex R) (moduleCone R C f)

/-- 全 Hom 円錐の左包含を閉単位に制限して取り出した元は、同じ左包含元。 -/
lemma dgGluingModuleConeLeftUnitElement :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCochainElement (moduleHom R C U K)
      ((Cochain.ofHom (eId (Complex R) U)).comp
        (moduleHomConeLeftCochain R C P f) (zero_add (-1))) =
      moduleConeInlElement R C f := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCochainElement, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    ModuleCat.comp_apply]
  change (moduleHomConeLeftCochain R C P f).v 0 (-1) rfl
    (unitElement R U).val = _
  rw [moduleHomConeLeftCochain, modulePostcompositionMap_apply, compose_unit]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
