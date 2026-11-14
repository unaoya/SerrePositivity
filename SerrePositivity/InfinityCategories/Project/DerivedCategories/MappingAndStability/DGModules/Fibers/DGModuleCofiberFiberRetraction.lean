module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleCofiberFiberLift
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleCycleFaithful
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleFiberNullHomotopy

/-! # dg 加群の cofiber と fiber の比較の実逆射

概要：fiber(inr f) から M への閉射を cone の第一射影と零ホモトピーから作る。
方針：全 Hom end の Leibniz 則と cone の行列恒等式を使う。
規約：比較との一方の合成は厳密に恒等。使われ方：β3 の実比較辺の同値性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}

/-- 比較の逆射の全 Hom end の次数零成分。 -/
def dgModuleCofiberFiberRetractElement (f : M ⟶ N) :
    GradedHom A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D (moduleConeInr A D f))
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M) 0 :=
  _root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.moduleConeFstElement A D f)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberNullHomotopy A D (moduleConeInr A D f)) (by decide)

/-- 逆射の候補成分は閉じている。 -/
lemma dgModuleCofiberFiberRetractElement_closed (f : M ⟶ N) :
    (moduleHom A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D (moduleConeInr A D f))
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M)).d 0 1
        (dgModuleCofiberFiberRetractElement A D f) = 0 := by
  have hn : _root_.SerrePositivity.DifferentialGraded.differential (D := _root_.SerrePositivity.DifferentialGraded.RightModule A D) A
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberNullHomotopy A D (moduleConeInr A D f)) =
      _root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.moduleConeInrElement A D f)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjectionElement A D (moduleConeInr A D f)) (zero_add 0) := by
    have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberNullHomotopy_differential A D (moduleConeInr A D f)
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleClosedCycle_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection_cycle] at h
    exact h
  have hz : _root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.moduleConeFstElement A D f)
      (_root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.moduleConeInrElement A D f)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjectionElement A D (moduleConeInr A D f)) (zero_add 0))
      (zero_add 1) = 0 := by
    rw [compose_assoc, moduleCone_inr_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose]
  change _root_.SerrePositivity.DifferentialGraded.differential A (dgModuleCofiberFiberRetractElement A D f) = 0
  rw [dgModuleCofiberFiberRetractElement, _root_.SerrePositivity.DifferentialGraded.differential_compose,
    show _root_.SerrePositivity.DifferentialGraded.differential (D := _root_.SerrePositivity.DifferentialGraded.RightModule A D) A (_root_.SerrePositivity.DifferentialGraded.moduleConeFstElement A D f) = 0 from
      moduleConeFstElement_d A D f, hn, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose]
  simp only [zero_add, hz, smul_zero]

/-- fiber(inr f) から元の始域への実閉加群射。 -/
def dgModuleCofiberFiberRetract (f : M ⟶ N) :
    ForgetEnrichment.of (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D (moduleConeInr A D f)) ⟶ M :=
  _root_.SerrePositivity.DifferentialGraded.moduleMorphismOfCycle A D (dgModuleCofiberFiberRetractElement A D f)
    (dgModuleCofiberFiberRetractElement_closed A D f)

/-- 閉逆射の成分は指定した次数零成分。 -/
lemma dgModuleCofiberFiberRetract_cycle (f : M ⟶ N) :
    (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) (dgModuleCofiberFiberRetract A D f))).val =
      dgModuleCofiberFiberRetractElement A D f := _root_.SerrePositivity.DifferentialGraded.moduleMorphismOfCycle_cycle A D _ _

/-- 比較の後に逆射を合成すると厳密に元の恒等射となる。 -/
lemma dgModuleCofiberFiberLift_retract (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberLift A D f ≫ dgModuleCofiberFiberRetract A D f = 𝟙 M := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleMorphism_ext_cycle A D
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleClosedCycle_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberLift_cycle,
    dgModuleCofiberFiberRetract_cycle, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleClosedCycle_id, dgModuleCofiberFiberRetractElement]
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum (A := A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberLiftElement A D f)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberNullHomotopy A D (moduleConeInr A D f)) (moduleConeFstElement A D f)
    (zero_add (-1)) (show (-1) + 1 = 0 by decide) (show 0 + (-1) + 1 = 0 by decide)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberLift_nullHomotopy_element, moduleCone_inl_fst] at h
  exact h.symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
