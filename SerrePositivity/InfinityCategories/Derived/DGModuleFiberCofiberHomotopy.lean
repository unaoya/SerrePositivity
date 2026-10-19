module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFiberCofiberHomotopyFirst
public import SerrePositivity.InfinityCategories.Derived.DGModuleConeLiftDifferential

/-! # 双対比較の合成の実原始元

概要：第一成分 −T⋅snd(g) と零第二成分から Q の次数 −1 自己射を作る。
方針：cone lift の行列微分と第一成分の射影式を使う。
規約：g=projection(f)、Q=cone(g)。使われ方：β3 の双対比較の同値性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D}

/-- 降下の後の逆射と恒等の差を解く次数 −1 成分。 -/
def dgModuleFiberCofiberHomotopyElement (f : M ⟶ N) :
    GradedHom A
      (ForgetEnrichment.to (Complex A) (moduleCone A D (dgModuleFiberProjection A D f)))
      (ForgetEnrichment.to (Complex A) (moduleCone A D (dgModuleFiberProjection A D f))) (-1) :=
  moduleConeLiftElement A D (dgModuleFiberProjection A D f) (-1)
    (dgModuleFiberCofiberHomotopyFirst A D f) 0

/-- 原始元の微分の二つの cone 成分。 -/
lemma dgModuleFiberCofiberHomotopyElement_differential_coordinates (f : M ⟶ N) :
    (moduleHom A D
      (ForgetEnrichment.to (Complex A) (moduleCone A D (dgModuleFiberProjection A D f)))
      (ForgetEnrichment.to (Complex A) (moduleCone A D (dgModuleFiberProjection A D f)))).d (-1) 0
        (dgModuleFiberCofiberHomotopyElement A D f) =
      moduleConeLiftElement A D (dgModuleFiberProjection A D f) 0
        (-(moduleHom A D
          (ForgetEnrichment.to (Complex A) (moduleCone A D (dgModuleFiberProjection A D f)))
          (dgModuleFiber A D f)).d 0 1 (dgModuleFiberCofiberHomotopyFirst A D f))
        (-moduleConeSndElement A D (dgModuleFiberProjection A D f)) := by
  have h := dgModuleConeLiftElement_differential A D (dgModuleFiberProjection A D f) (-1)
    (dgModuleFiberCofiberHomotopyFirst A D f) 0
  change (moduleHom A D
    (ForgetEnrichment.to (Complex A) (moduleCone A D (dgModuleFiberProjection A D f)))
    (ForgetEnrichment.to (Complex A) (moduleCone A D (dgModuleFiberProjection A D f)))).d (-1) 0
      (dgModuleFiberCofiberHomotopyElement A D f) =
    moduleConeLiftElement A D (dgModuleFiberProjection A D f) 0
      (-(moduleHom A D
        (ForgetEnrichment.to (Complex A) (moduleCone A D (dgModuleFiberProjection A D f)))
        (dgModuleFiber A D f)).d 0 1 (dgModuleFiberCofiberHomotopyFirst A D f))
      ((moduleHom A D
        (ForgetEnrichment.to (Complex A) (moduleCone A D (dgModuleFiberProjection A D f)))
        (ForgetEnrichment.to (Complex A) M)).d (-1) 0 0 +
       compose A (cycleFromUnit _
        (ForgetEnrichment.homTo (Complex A) (dgModuleFiberProjection A D f))).val
        (dgModuleFiberCofiberHomotopyFirst A D f) (zero_add 0)) at h
  rw [dgModuleFiberProjection_cycle, dgModuleFiberCofiberHomotopyFirst_projection, map_zero] at h
  simpa only [zero_add] using h

end SerrePositivity.InfinityCategories
