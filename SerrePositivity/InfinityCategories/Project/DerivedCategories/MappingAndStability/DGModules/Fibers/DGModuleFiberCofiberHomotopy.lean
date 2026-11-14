module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleFiberCofiberHomotopyFirst
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleConeLiftDifferential

/-! # 双対比較の合成の実原始元

概要：第一成分 −T⋅snd(g) と零第二成分から Q の次数 −1 自己射を作る。
方針：cone lift の行列微分と第一成分の射影式を使う。
規約：g=projection(f)、Q=cone(g)。使われ方：β3 の双対比較の同値性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}

/-- 降下の後の逆射と恒等の差を解く次数 −1 成分。 -/
def dgModuleFiberCofiberHomotopyElement (f : M ⟶ N) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom A
      (ForgetEnrichment.to (Complex A) (moduleCone A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f)))
      (ForgetEnrichment.to (Complex A) (moduleCone A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f))) (-1) :=
  moduleConeLiftElement A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f) (-1)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberHomotopyFirst A D f) 0

/-- 原始元の微分の二つの cone 成分。 -/
lemma dgModuleFiberCofiberHomotopyElement_differential_coordinates (f : M ⟶ N) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom A D
      (ForgetEnrichment.to (Complex A) (moduleCone A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f)))
      (ForgetEnrichment.to (Complex A) (moduleCone A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f)))).d (-1) 0
        (dgModuleFiberCofiberHomotopyElement A D f) =
      moduleConeLiftElement A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f) 0
        (-(_root_.SerrePositivity.DifferentialGraded.moduleHom A D
          (ForgetEnrichment.to (Complex A) (moduleCone A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f)))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f)).d 0 1 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberHomotopyFirst A D f))
        (-moduleConeSndElement A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeLiftElement_differential A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f) (-1)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberHomotopyFirst A D f) 0
  change (_root_.SerrePositivity.DifferentialGraded.moduleHom A D
    (ForgetEnrichment.to (Complex A) (moduleCone A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f)))
    (ForgetEnrichment.to (Complex A) (moduleCone A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f)))).d (-1) 0
      (dgModuleFiberCofiberHomotopyElement A D f) =
    moduleConeLiftElement A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f) 0
      (-(_root_.SerrePositivity.DifferentialGraded.moduleHom A D
        (ForgetEnrichment.to (Complex A) (moduleCone A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f)))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f)).d 0 1 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberHomotopyFirst A D f))
      ((_root_.SerrePositivity.DifferentialGraded.moduleHom A D
        (ForgetEnrichment.to (Complex A) (moduleCone A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f)))
        (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M)).d (-1) 0 0 +
       _root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _
        (ForgetEnrichment.homTo (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f))).val
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberHomotopyFirst A D f) (zero_add 0)) at h
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection_cycle, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberHomotopyFirst_projection, map_zero] at h
  simpa only [zero_add] using h

end SerrePositivity.InfinityCategories.Project.DerivedCategories
