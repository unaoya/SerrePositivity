module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.Parameter
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.SphereClosure
public import SerrePositivity.KST.SConstruction.DGModuleExtensionInputHomComposition

/-!
概要：入力 dg 関手の全次数変換を、新 sphere-only 閉包の厳密関手間へ移す。
方針：元の実延長のパラメータ作用を、選んだ閉包代表へ共役する。
規約：ここでは cone まで。cell 分解と商への全次数延長は別工程。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
open CategoryTheory DifferentialGraded KST.SConstruction
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 < κ) (hreg : κ.IsRegular)

/-- 入力の任意複体パラメータを保った、新閉包関手間の全次数作用。 -/
def dgKappaSphereClosureExtensionParameter {K : Complex R} {F G : DGFunctor R C D}
    (τ : DGFunctorParamTrans R C D K F G) :
    DGFunctorParamTrans R {M // _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects R C κ M}
      {N // _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects R D κ N} K
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaSphereClosureExtensionFunctor R C D F hκ hreg)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaSphereClosureExtensionFunctor R C D G hκ hreg) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaSphereClosureExtensionStrictImage R C D F hκ hreg).parameter R C D _ _ _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaSphereClosureExtensionStrictImage R C D G hκ hreg)
    (dgModuleExtensionParameter R C D τ)

attribute [local instance] _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects_small

/-- 入力 Hom 複体から、新閉包関手圏の Hom 複体への鎖写像。 -/
def dgKappaSphereClosureExtensionInputHom (F G : DGFunctor R C D) :
    dgFunctorHom R C D F G ⟶
      dgFunctorHom R {M // _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects R C κ M}
        {N // _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects R D κ N}
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaSphereClosureExtensionFunctor R C D F hκ hreg)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaSphereClosureExtensionFunctor R C D G hκ hreg) :=
  (dgFunctorHomEquiv R _ _ _ _ _).symm
    (dgKappaSphereClosureExtensionParameter R C D hκ hreg
      (dgFunctorHomEquiv R C D _ F G (𝟙 _)))

/-- 各対象で、元の入力 Hom 作用を同じ閉比較で共役した式を回収する。 -/
@[reassoc] lemma dgKappaSphereClosureExtensionInputHom_π (F G : DGFunctor R C D)
    (M : {M // _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects R C κ M}) :
    dgKappaSphereClosureExtensionInputHom R C D hκ hreg F G ≫
      dgFunctorHomπ R _ _ _ _ M =
    dgModuleExtensionInputHom R C D F G (ForgetEnrichment.to (Complex R) M.val) ≫
      enrichedClosedIsoConjugation (Complex R)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaSphereClosureExtensionStrictImage R C D F hκ hreg).iso M)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaSphereClosureExtensionStrictImage R C D G hκ hreg).iso M) := by
  rw [dgKappaSphereClosureExtensionInputHom, dgFunctorHomEquiv_symm_π]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
