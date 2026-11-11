module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGProjectiveDerivedComparison
public import SerrePositivity.DifferentialGraded.Derived.Projective
/-!
概要：射影的模型の主導来比較を標準分解関手で戻すと、元の同じ H⁰ 包含と自然同型。
方針：実増大のホモトピー同型と lift 方程式を、境界商の自然同型として降ろす。
規約：対象別同型だけで済ませない。使われ方：β5 の既存の導来 Morita 同値の移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
/-- 射影的加群の H⁰ 比較と元の主局所化の、閉零射上の同じ自然比較。 -/
def dgProjectiveModuleToDerived_fac :
    toHomotopy R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D) ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleToDerived R D ≅
      (dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D)).onClosed ⋙
        moduleToDerived R D := by
  let I := dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D)
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (eqToIso I.onHomotopy_fac) (moduleHomotopyToDerivedClosed R D) ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft I.onClosed (moduleToHomotopyDerivedIso R D)
/-- 射影的加群に制限した標準分解の実増大は、H⁰ の同じ自然同型。 -/
def dgProjectiveResolutionAugmentationIso :
    (dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D)).onClosed ⋙
      moduleResolutionHomotopyFunctor R D (moduleCanonicalProjectiveResolution R D) ≅
    (dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D)).onClosed ⋙
      moduleToHomotopy R D := by
  let I := dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D)
  have hi (X : ClosedCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D)) :
      IsIso ((moduleToHomotopy R D).map
        (moduleCanonicalProjectiveResolution R D (I.onClosed.obj X)).π) :=
    moduleHomotopicallyProjective_quasiIso_isIso_homotopy R D
      (moduleCanonicalProjectiveResolution R D (I.onClosed.obj X)).projective
      (ForgetEnrichment.to (Complex R) X).property _
      (moduleCanonicalProjectiveResolution R D (I.onClosed.obj X)).quasiIso
  exact NatIso.ofComponents (fun X => by
    have := hi X
    exact asIso ((moduleToHomotopy R D).map
      (moduleCanonicalProjectiveResolution R D (I.onClosed.obj X)).π)) (by
    intro X Y f
    exact (moduleCanonicalProjectiveResolution R D (I.onClosed.obj X)).lift_fac
      (moduleCanonicalProjectiveResolution R D (I.onClosed.obj Y)) (I.onClosed.map f))
/-- 射影的模型の主導来比較を標準分解で戻すと、元の同じ H⁰ 包含と自然同型。 -/
def dgProjectiveDerivedResolutionIso :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleToDerived R D ⋙
      moduleDerivedResolutionFunctor R D (moduleCanonicalProjectiveResolution R D) ≅
    (dgFullSubcategoryInclusion R (RightModule R D)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D)).onHomotopy := by
  let I := dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D)
  apply CategoryTheory.Quotient.natIsoLift
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (dgProjectiveModuleToDerived_fac R D)
      (moduleDerivedResolutionFunctor R D (moduleCanonicalProjectiveResolution R D)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft I.onClosed
      (moduleDerivedResolutionFunctor_fac R D (moduleCanonicalProjectiveResolution R D)) ≪≫
    dgProjectiveResolutionAugmentationIso R D ≪≫ (eqToIso I.onHomotopy_fac).symm
end SerrePositivity.InfinityCategories.Project.DerivedCategories
