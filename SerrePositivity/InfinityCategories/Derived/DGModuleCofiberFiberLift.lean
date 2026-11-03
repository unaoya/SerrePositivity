module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFiberHomDifferential
public import SerrePositivity.InfinityCategories.Derived.DGModuleFiberHomProjections
public import SerrePositivity.InfinityCategories.Derived.DGModuleConeSquare
public import SerrePositivity.DifferentialGraded.Module.ConeConstruction

/-! # dg 加群の標準 cofiber から fiber への実比較射

概要：M から fiber(N→cone(f)) への閉加群射を二成分で構成する。
方針：実射 f と次数 −1 の cone 包含を fiber の逆座標へ入れる。
規約：射影と零ホモトピーの両方を厳密に保持する。使われ方：β3 の安定性判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D}

/-- 標準 cofiber の始域から fiber への比較の次数零成分。 -/
def dgModuleCofiberFiberLiftElement (f : M ⟶ N) :
    GradedHom A (ForgetEnrichment.to (Complex A) M)
      (dgModuleFiber A D (moduleConeInr A D f)) 0 :=
  (dgModuleFiberHomCoordinates A D M (moduleConeInr A D f) (-1)).symm
    ((cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val, moduleConeInlElement A D f)

/-- 比較成分は全 Hom end 内で閉じている。 -/
lemma dgModuleCofiberFiberLiftElement_closed (f : M ⟶ N) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (dgModuleFiber A D (moduleConeInr A D f))).d 0 1
        (dgModuleCofiberFiberLiftElement A D f) = 0 := by
  change differential A (dgModuleCofiberFiberLiftElement A D f) = 0
  rw [dgModuleCofiberFiberLiftElement, dgModuleFiberHomCoordinates_symm_differential]
  have hc : (moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N)).d 0 1
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val = 0 :=
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).property
  have hi : (moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) (moduleCone A D f))).d (-1) 0
      (moduleConeInlElement A D f) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
        (f ≫ moduleConeInr A D f))).val := moduleConeInlElement_d A D f
  have hs : compose A
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (moduleConeInr A D f))).val
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val (zero_add 0) -
      (moduleHom A D (ForgetEnrichment.to (Complex A) M)
        (ForgetEnrichment.to (Complex A) (moduleCone A D f))).d (-1) 0
          (moduleConeInlElement A D f) = 0 := by
    rw [hi, dgModuleClosedCycle_comp, sub_self]
  exact (congrArg (dgModuleFiberHomCoordinates A D M (moduleConeInr A D f) 0).symm
    (Prod.ext hc hs)).trans
      (dgModuleFiberHomCoordinates A D M (moduleConeInr A D f) 0).symm.map_zero

/-- 標準 cone の始域からその右辺の fiber への閉加群射。 -/
def dgModuleCofiberFiberLift (f : M ⟶ N) :
    M ⟶ ForgetEnrichment.of (Complex A) (dgModuleFiber A D (moduleConeInr A D f)) :=
  moduleMorphismOfCycle A D (dgModuleCofiberFiberLiftElement A D f)
    (dgModuleCofiberFiberLiftElement_closed A D f)

/-- 閉射に戻した比較の全 Hom 成分は指定した逆座標。 -/
lemma dgModuleCofiberFiberLift_cycle (f : M ⟶ N) :
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (dgModuleCofiberFiberLift A D f))).val =
      dgModuleCofiberFiberLiftElement A D f := moduleMorphismOfCycle_cycle A D _ _

/-- 比較射の射影成分は元の実加群射の成分。 -/
lemma dgModuleCofiberFiberLift_projection_element (f : M ⟶ N) :
    compose A (dgModuleFiberProjectionElement A D (moduleConeInr A D f))
      (dgModuleCofiberFiberLiftElement A D f) (zero_add 0) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val :=
  dgModuleFiberHomCoordinates_symm_projection A D (moduleConeInr A D f) (-1) _ _

/-- 比較射の零ホモトピー成分は元の cone 包含。 -/
lemma dgModuleCofiberFiberLift_nullHomotopy_element (f : M ⟶ N) :
    compose A (dgModuleFiberNullHomotopy A D (moduleConeInr A D f))
      (dgModuleCofiberFiberLiftElement A D f) (zero_add (-1)) = moduleConeInlElement A D f :=
  dgModuleFiberHomCoordinates_symm_nullHomotopy A D (moduleConeInr A D f) (-1) _ _

end SerrePositivity.InfinityCategories
