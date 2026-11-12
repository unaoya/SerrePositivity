module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.ModuleExtension
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaSphereClosureOperations

/-!
概要：D-3 の実閉包関手化を、D-2 が公開した sphere-free 閉包集合へ特殊化する。
方針：同じ ordinal・次数の基底ラベル写像と標準実同型を一般入口へ渡す。
規約：新 cone・段提供者の選択は行わない。D-4a の全単体作用は別工程。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (F : DGFunctor R C D)
  {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 < κ) (hreg : κ.IsRegular)

/-- 新 cone の objects と定義上一致する、sphere-free 閉包の実像比較。 -/
def dgKappaSphereClosureExtensionStrictImage :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.DGModuleStrictImage R C D (dgModuleExtension R C D F)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects R C κ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects R D κ) := by
  let : Nonempty κ.ord.ToType :=
    Cardinal.nonempty_ord_toType (ne_of_gt (lt_trans Cardinal.aleph0_pos hκ))
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgModuleExtensionClosureStrictImage R C D F
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.kappaOrdinal_countable_strict_bound hκ hreg)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureBaseFamily R C κ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureBaseFamily R D κ)
    (fun i => ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereFreeLabelMap R F i, ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaSphereFreeExtensionIso R C D F i⟩⟩)

/-- D-3 の新 objects 集合間の厳密 dg 関手。 -/
def dgKappaSphereClosureExtensionFunctor :
    DGFunctor R {M // _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects R C κ M}
      {N // _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects R D κ N} :=
  (dgKappaSphereClosureExtensionStrictImage R C D F hκ hreg).functor R C D _ _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
