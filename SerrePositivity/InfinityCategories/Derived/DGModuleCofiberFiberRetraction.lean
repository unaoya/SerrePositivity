module
public import SerrePositivity.InfinityCategories.Derived.DGModuleCofiberFiberLift
public import SerrePositivity.InfinityCategories.Derived.DGModuleCycleFaithful
public import SerrePositivity.InfinityCategories.Derived.DGModuleFiberNullHomotopy

/-! # dg 加群の cofiber と fiber の比較の実逆射

概要：fiber(inr f) から M への閉射を cone の第一射影と零ホモトピーから作る。
方針：全 Hom end の Leibniz 則と cone の行列恒等式を使う。
規約：比較との一方の合成は厳密に恒等。使われ方：β3 の実比較辺の同値性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D}

/-- 比較の逆射の全 Hom end の次数零成分。 -/
def dgModuleCofiberFiberRetractElement (f : M ⟶ N) :
    GradedHom A (dgModuleFiber A D (moduleConeInr A D f))
      (ForgetEnrichment.to (Complex A) M) 0 :=
  compose A (moduleConeFstElement A D f)
    (dgModuleFiberNullHomotopy A D (moduleConeInr A D f)) (by decide)

/-- 逆射の候補成分は閉じている。 -/
lemma dgModuleCofiberFiberRetractElement_closed (f : M ⟶ N) :
    (moduleHom A D (dgModuleFiber A D (moduleConeInr A D f))
      (ForgetEnrichment.to (Complex A) M)).d 0 1
        (dgModuleCofiberFiberRetractElement A D f) = 0 := by
  have hn : differential (D := RightModule A D) A
      (dgModuleFiberNullHomotopy A D (moduleConeInr A D f)) =
      compose A (moduleConeInrElement A D f)
        (dgModuleFiberProjectionElement A D (moduleConeInr A D f)) (zero_add 0) := by
    have h := dgModuleFiberNullHomotopy_differential A D (moduleConeInr A D f)
    rw [dgModuleClosedCycle_comp, dgModuleFiberProjection_cycle] at h
    exact h
  have hz : compose A (moduleConeFstElement A D f)
      (compose A (moduleConeInrElement A D f)
        (dgModuleFiberProjectionElement A D (moduleConeInr A D f)) (zero_add 0))
      (zero_add 1) = 0 := by
    rw [compose_assoc, moduleCone_inr_fst, zero_compose]
  change differential A (dgModuleCofiberFiberRetractElement A D f) = 0
  rw [dgModuleCofiberFiberRetractElement, differential_compose,
    show differential (D := RightModule A D) A (moduleConeFstElement A D f) = 0 from
      moduleConeFstElement_d A D f, hn, zero_compose]
  simp only [zero_add, hz, smul_zero]

/-- fiber(inr f) から元の始域への実閉加群射。 -/
def dgModuleCofiberFiberRetract (f : M ⟶ N) :
    ForgetEnrichment.of (Complex A) (dgModuleFiber A D (moduleConeInr A D f)) ⟶ M :=
  moduleMorphismOfCycle A D (dgModuleCofiberFiberRetractElement A D f)
    (dgModuleCofiberFiberRetractElement_closed A D f)

/-- 閉逆射の成分は指定した次数零成分。 -/
lemma dgModuleCofiberFiberRetract_cycle (f : M ⟶ N) :
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (dgModuleCofiberFiberRetract A D f))).val =
      dgModuleCofiberFiberRetractElement A D f := moduleMorphismOfCycle_cycle A D _ _

/-- 比較の後に逆射を合成すると厳密に元の恒等射となる。 -/
lemma dgModuleCofiberFiberLift_retract (f : M ⟶ N) :
    dgModuleCofiberFiberLift A D f ≫ dgModuleCofiberFiberRetract A D f = 𝟙 M := by
  apply dgModuleMorphism_ext_cycle A D
  rw [dgModuleClosedCycle_comp, dgModuleCofiberFiberLift_cycle,
    dgModuleCofiberFiberRetract_cycle, dgModuleClosedCycle_id, dgModuleCofiberFiberRetractElement]
  have h := compose_assoc_of_sum (A := A) (dgModuleCofiberFiberLiftElement A D f)
    (dgModuleFiberNullHomotopy A D (moduleConeInr A D f)) (moduleConeFstElement A D f)
    (zero_add (-1)) (show (-1) + 1 = 0 by decide) (show 0 + (-1) + 1 = 0 by decide)
  rw [dgModuleCofiberFiberLift_nullHomotopy_element, moduleCone_inl_fst] at h
  exact h.symm

end SerrePositivity.InfinityCategories
