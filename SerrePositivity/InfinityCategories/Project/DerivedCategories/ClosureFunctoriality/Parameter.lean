module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.FullFunctor
public import SerrePositivity.DifferentialGraded.Functor.DGParameterConjugation
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorHomPrecomposition

/-!
概要：閉包代表の実比較を使い、全次数パラメータ変換を充満部分圏間へ移す。
方針：元の変換を包含で制限し、保持した閉同型で全 Hom 共役する。
規約：任意の複体パラメータを扱う。閉零変換へ制限しない。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
open CategoryTheory DifferentialGraded KST.NonConnective KST.SConstruction
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D]
  (F G : DGFunctor R (RightModule R C) (RightModule R D))
  (S : Set (ModuleCategory R C)) (T : Set (ModuleCategory R D))
  (I : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.DGModuleStrictImage R C D F S T) (J : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.DGModuleStrictImage R C D G S T)

/-- 任意の全次数変換を、同じ実比較による閉包関手間の変換へ送る。 -/
def DGModuleStrictImage.parameter {K : Complex R}
    (τ : DGFunctorParamTrans R (RightModule R C) (RightModule R D) K F G) :
    DGFunctorParamTrans R {M // S M} {N // T N} K
      (I.functor R C D F S T) (J.functor R C D G S T) := by
  let H := (dgFullSubcategoryInclusion R (ModuleCategory R C) S).comp
    (dgConeModuleForget R C)
  let α := dgFunctorClosedConjugateParameter R (H.comp F) (H.comp G)
    (fun M => ForgetEnrichment.to (Complex R) (I.obj M).val)
    (fun M => ForgetEnrichment.to (Complex R) (J.obj M).val) I.iso J.iso
    (dgFunctorParamPre R _ _ _ H τ)
  exact { app := α.app, naturality := α.naturality }

/-- 各成分は元の同じパラメータ作用を、両端の実比較同型で共役した鎖写像。 -/
lemma DGModuleStrictImage.parameter_app {K : Complex R}
    (τ : DGFunctorParamTrans R (RightModule R C) (RightModule R D) K F G)
    (M : {M // S M}) :
    (I.parameter R C D F G S T J τ).app M =
      τ.app (ForgetEnrichment.to (Complex R) M.val) ≫
        enrichedClosedIsoConjugation (Complex R) (I.iso M) (J.iso M) := rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
