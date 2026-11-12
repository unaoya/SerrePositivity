module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFiberCofiberSectionFirst
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleConeLiftDifferential
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleConeLiftProjections
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFiberCofiberDesc
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleCycleFaithful

/-! # fiber の cofiber 比較の実閉逆射

概要：N→cone(projection f) を閉次数零の cone lift から構成する。
方針：第一成分の閉性と射影による消滅を cone の行列微分へ代入する。
規約：降下との一方の合成は厳密に恒等。使われ方：β3 の双対比較の同値性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}

/-- 逆射の閉零成分は第一成分と零第二成分の cone lift。 -/
def dgModuleFiberCofiberSectionElement (f : M ⟶ N) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) N)
      (ForgetEnrichment.to (Complex A) (moduleCone A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f))) 0 :=
  moduleConeLiftElement A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f) 0
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberSectionFirst A D f) 0

/-- 逆射の成分は閉じている。 -/
lemma dgModuleFiberCofiberSectionElement_closed (f : M ⟶ N) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom A D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) N)
      (ForgetEnrichment.to (Complex A) (moduleCone A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f)))).d 0 1
        (dgModuleFiberCofiberSectionElement A D f) = 0 := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeLiftElement_differential A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f) 0
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberSectionFirst A D f) 0
  have ha := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberSectionFirst_closed A D f
  have hp : _root_.SerrePositivity.DifferentialGraded.compose A
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f))).val
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberSectionFirst A D f) (add_zero 1) = 0 := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection_cycle]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberSectionFirst_projection A D f
  change (_root_.SerrePositivity.DifferentialGraded.moduleHom A D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) N)
    (ForgetEnrichment.to (Complex A) (moduleCone A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f)))).d 0 1
      (dgModuleFiberCofiberSectionElement A D f) =
    moduleConeLiftElement A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f) 1
      (-(moduleHom A D (ForgetEnrichment.to (Complex A) N) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f)).d 1 2
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberSectionFirst A D f))
      ((_root_.SerrePositivity.DifferentialGraded.moduleHom A D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) N)
        (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M)).d 0 1 0 +
       _root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _
        (ForgetEnrichment.homTo (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f))).val
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberSectionFirst A D f) (add_zero 1)) at h
  rw [ha, hp, map_zero, neg_zero, add_zero] at h
  exact h.trans (by simp only [_root_.SerrePositivity.DifferentialGraded.moduleConeLiftElement, _root_.SerrePositivity.DifferentialGraded.complexConeElementMk, map_zero, add_zero])

/-- fiber の射影の cone への実閉加群射。 -/
def dgModuleFiberCofiberSection (f : M ⟶ N) :
    N ⟶ moduleCone A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f) :=
  _root_.SerrePositivity.DifferentialGraded.moduleMorphismOfCycle A D (dgModuleFiberCofiberSectionElement A D f)
    (dgModuleFiberCofiberSectionElement_closed A D f)

/-- 閉逆射の全 Hom end の成分。 -/
lemma dgModuleFiberCofiberSection_cycle (f : M ⟶ N) :
    (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) (dgModuleFiberCofiberSection A D f))).val =
      dgModuleFiberCofiberSectionElement A D f := _root_.SerrePositivity.DifferentialGraded.moduleMorphismOfCycle_cycle A D _ _

/-- 逆射の第一 cone 射影は指定した第一成分。 -/
lemma dgModuleFiberCofiberSection_fst (f : M ⟶ N) :
    compose A (moduleConeFstElement A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f))
      (dgModuleFiberCofiberSectionElement A D f) (zero_add 1) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberSectionFirst A D f := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeLiftElement_fst A D _ 0 _ _

/-- 逆射の第二 cone 射影は零。 -/
lemma dgModuleFiberCofiberSection_snd (f : M ⟶ N) :
    compose A (moduleConeSndElement A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f))
      (dgModuleFiberCofiberSectionElement A D f) (zero_add 0) = 0 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeLiftElement_snd A D _ 0 _ _

/-- 逆射の後の降下比較は厳密に N の恒等射。 -/
lemma dgModuleFiberCofiberSection_desc (f : M ⟶ N) :
    dgModuleFiberCofiberSection A D f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberDesc A D f = 𝟙 N := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleMorphism_ext_cycle A D
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleClosedCycle_comp, dgModuleFiberCofiberSection_cycle,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberDesc_cycle, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleClosedCycle_id,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeDescElement, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_add_left, ← compose_assoc, ← compose_assoc,
    dgModuleFiberCofiberSection_fst, dgModuleFiberCofiberSection_snd,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, add_zero]
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberSectionFirst_nullHomotopy A D f
  · omega

end SerrePositivity.InfinityCategories.Project.DerivedCategories
