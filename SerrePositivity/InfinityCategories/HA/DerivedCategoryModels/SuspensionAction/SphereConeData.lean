module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.ConeData
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.SphereClosure
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.SphereClosureConeInput

/-!
概要：D-2 のコミット済み sphere-only cone 入力に、実延長の strict data を供給する。
方針：objects の定義上の一致で D-3 の実像比較を正本 ofConeFunctor へ渡す。
規約：段提供者を選ばず、全入力の map・edgeIso は別途供給する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction
open CategoryTheory DifferentialGraded KST.NonConnective
variable (R : Type u) [CommRing R] (C D : Type v)
  [DGCategory R C] [Small.{u} C] [DGCategory R D] [Small.{u} D]
  (F : DGFunctor R C D) (κ : Cardinal.{u}) [Fact κ.IsRegular]
  (hκ : Cardinal.aleph0 < κ)

/-- D-2 の同じ新 cone 間における、任意の実 dg 関手の K-B3 strict data。 -/
def dgKappaSphereClosureSuspensionMapData :
    DGKappaSuspensionMapData R C D
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R C κ hκ)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R D κ hκ) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgModuleStrictImageSuspensionMapData R C D F
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R C κ hκ)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R D κ hκ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaSphereClosureExtensionStrictImage R C D F hκ Fact.out)

/-- strict data の cone は D-3 の同じ全 Hom 共役関手である。 -/
lemma dgKappaSphereClosureSuspensionMapData_cone :
    (dgKappaSphereClosureSuspensionMapData R C D F κ hκ).cone =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaSphereClosureExtensionFunctor R C D F hκ Fact.out := rfl

/-- 新 cone の元の perfect 対象集合を、同じ実導来 perfect 性の意味で保つ。 -/
lemma dgKappaSphereClosureSuspensionMapData_preservesPerfect
    (M : DGKappaCone R C (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R C κ hκ))
    (hM : M ∈ dgKappaConePerfectObjects R C (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R C κ hκ)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaSphereClosureExtensionFunctor R C D F hκ Fact.out).obj M ∈
      dgKappaConePerfectObjects R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R D κ hκ) :=
  (dgKappaSphereClosureSuspensionMapData R C D F κ hκ).preservesPerfect M hM

/-- 同じ平坦分解と実商への正本 dg 入力射。 -/
def dgKappaSphereClosureSuspensionInputMap :
    dgKappaSuspensionKInput R C (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R C κ hκ) ⟶
      dgKappaSuspensionKInput R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R D κ hκ) :=
  dgKappaSuspensionInputMap R C D
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R C κ hκ)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R D κ hκ)
    (dgKappaSphereClosureSuspensionMapData R C D F κ hκ)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction
