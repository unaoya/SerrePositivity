module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSubcategoryPretriangulated
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaSphereClosureOperations
/-!
概要：正則非可算 κ の選択射影代表系の前三角性。
方針：構成済みの同じ零・shift・cone 閉性を一般判定へ渡す。
規約：κ-compact 性と全 κ-compact 頂点の被覆は別工程。
使われ方：DGKappaConeInput の pretriangulated フィールド。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
section
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
attribute [local instance] _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects_small

lemma dgKappaSphereClosureObjects_isDGPretriangulated {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 < κ) (hreg : κ.IsRegular) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R {M // _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects R D κ M} := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSubcategory_isDGPretriangulated R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects R D κ)
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects_zero R D hκ
  · intro M hM n
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects_shift R D hκ hreg M hM n
  · intro M N hM hN f
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects_cone R D hκ hreg M N hM hN f
end

end SerrePositivity.InfinityCategories.Project.DerivedCategories
