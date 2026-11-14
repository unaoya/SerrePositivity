module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleFiberHomDifferential
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleFiberHomProjections
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleConeSquare
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}

/-- 標準 cofiber の始域から fiber への比較の次数零成分。 -/
def dgModuleCofiberFiberLiftElement (f : M ⟶ N) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D (moduleConeInr A D f)) 0 :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberHomCoordinates A D M (moduleConeInr A D f) (-1)).symm
    ((_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) f)).val, _root_.SerrePositivity.DifferentialGraded.moduleConeInlElement A D f)

/-- 比較成分は全 Hom end 内で閉じている。 -/
lemma dgModuleCofiberFiberLiftElement_closed (f : M ⟶ N) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom A D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D (moduleConeInr A D f))).d 0 1
        (dgModuleCofiberFiberLiftElement A D f) = 0 := by
  change _root_.SerrePositivity.DifferentialGraded.differential A (dgModuleCofiberFiberLiftElement A D f) = 0
  rw [dgModuleCofiberFiberLiftElement, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberHomCoordinates_symm_differential]
  have hc : (_root_.SerrePositivity.DifferentialGraded.moduleHom A D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) N)).d 0 1
      (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) f)).val = 0 :=
    (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) f)).property
  have hi : (_root_.SerrePositivity.DifferentialGraded.moduleHom A D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f))).d (-1) 0
      (_root_.SerrePositivity.DifferentialGraded.moduleConeInlElement A D f) =
      (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A)
        (f ≫ _root_.SerrePositivity.DifferentialGraded.moduleConeInr A D f))).val := _root_.SerrePositivity.DifferentialGraded.moduleConeInlElement_d A D f
  have hs : _root_.SerrePositivity.DifferentialGraded.compose A
      (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleConeInr A D f))).val
      (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) f)).val (zero_add 0) -
      (_root_.SerrePositivity.DifferentialGraded.moduleHom A D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M)
        (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f))).d (-1) 0
          (_root_.SerrePositivity.DifferentialGraded.moduleConeInlElement A D f) = 0 := by
    rw [hi, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleClosedCycle_comp, sub_self]
  exact (congrArg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberHomCoordinates A D M (moduleConeInr A D f) 0).symm
    (Prod.ext hc hs)).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberHomCoordinates A D M (moduleConeInr A D f) 0).symm.map_zero

/-- 標準 cone の始域からその右辺の fiber への閉加群射。 -/
def dgModuleCofiberFiberLift (f : M ⟶ N) :
    M ⟶ ForgetEnrichment.of (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D (moduleConeInr A D f)) :=
  _root_.SerrePositivity.DifferentialGraded.moduleMorphismOfCycle A D (dgModuleCofiberFiberLiftElement A D f)
    (dgModuleCofiberFiberLiftElement_closed A D f)

/-- 閉射に戻した比較の全 Hom 成分は指定した逆座標。 -/
lemma dgModuleCofiberFiberLift_cycle (f : M ⟶ N) :
    (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) (dgModuleCofiberFiberLift A D f))).val =
      dgModuleCofiberFiberLiftElement A D f := _root_.SerrePositivity.DifferentialGraded.moduleMorphismOfCycle_cycle A D _ _

/-- 比較射の射影成分は元の実加群射の成分。 -/
lemma dgModuleCofiberFiberLift_projection_element (f : M ⟶ N) :
    compose A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjectionElement A D (moduleConeInr A D f))
      (dgModuleCofiberFiberLiftElement A D f) (zero_add 0) =
      (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) f)).val :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberHomCoordinates_symm_projection A D (moduleConeInr A D f) (-1) _ _

/-- 比較射の零ホモトピー成分は元の cone 包含。 -/
lemma dgModuleCofiberFiberLift_nullHomotopy_element (f : M ⟶ N) :
    compose A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberNullHomotopy A D (moduleConeInr A D f))
      (dgModuleCofiberFiberLiftElement A D f) (zero_add (-1)) = moduleConeInlElement A D f :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberHomCoordinates_symm_nullHomotopy A D (moduleConeInr A D f) (-1) _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories
