module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleConeProjectionDifferential
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Algebra

/-! # shifted cone による dg 加群の fiber 対象と射影

概要：cone(f)[−1] と閉次数零の射影、合成を零にする実原始元を構成する。
方針：shift の閉斉次単位を cone の第一・第二射影に合成する。
規約：shift の斉次単位が持つ符号を保持する。使われ方：β3 の fiber 四角形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}

/-- 閉 dg 加群射の shifted cone としての fiber 対象。 -/
abbrev dgModuleFiber (f : M ⟶ N) : RightModule A D :=
  _root_.SerrePositivity.DifferentialGraded.shiftModule (-1) (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f))

/-- shifted cone から元の始点への次数零成分。 -/
def dgModuleFiberProjectionElement (f : M ⟶ N) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom A (dgModuleFiber A D f) (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M) 0 :=
  _root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.moduleConeFstElement A D f)
    (_root_.SerrePositivity.DifferentialGraded.moduleShiftOutElement A D (-1) (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f)))
    (by decide)

/-- 射影と元の射の合成の零ホモトピーを与える次数 −1 成分。 -/
def dgModuleFiberNullHomotopy (f : M ⟶ N) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom A (dgModuleFiber A D f) (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) N) (-1) :=
  -_root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.moduleConeSndElement A D f)
    (_root_.SerrePositivity.DifferentialGraded.moduleShiftOutElement A D (-1) (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f)))
    (by decide)

/-- shifted cone の射影成分は閉じている。 -/
lemma dgModuleFiberProjectionElement_closed (f : M ⟶ N) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom A D (dgModuleFiber A D f) (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M)).d 0 1
      (dgModuleFiberProjectionElement A D f) = 0 := by
  change _root_.SerrePositivity.DifferentialGraded.differential A (dgModuleFiberProjectionElement A D f) = 0
  rw [dgModuleFiberProjectionElement, _root_.SerrePositivity.DifferentialGraded.differential_compose]
  have hfst : _root_.SerrePositivity.DifferentialGraded.differential (D := _root_.SerrePositivity.DifferentialGraded.RightModule A D) A (_root_.SerrePositivity.DifferentialGraded.moduleConeFstElement A D f) = 0 :=
    _root_.SerrePositivity.DifferentialGraded.moduleConeFstElement_d A D f
  have hout : _root_.SerrePositivity.DifferentialGraded.differential (D := _root_.SerrePositivity.DifferentialGraded.RightModule A D) A
      (_root_.SerrePositivity.DifferentialGraded.moduleShiftOutElement A D (-1) (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f))) = 0 :=
    _root_.SerrePositivity.DifferentialGraded.moduleShiftOutElement_d A D (-1) _
  rw [hfst, hout, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, smul_zero, add_zero]

/-- 全 Hom end の閉成分から得る実際の fiber 射影の閉加群射。 -/
def dgModuleFiberProjection (f : M ⟶ N) :
    ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (dgModuleFiber A D f) ⟶ M :=
  _root_.SerrePositivity.DifferentialGraded.moduleMorphismOfCycle A D (dgModuleFiberProjectionElement A D f)
    (dgModuleFiberProjectionElement_closed A D f)

/-- 閉加群射へ戻した射影の成分は元の指定成分。 -/
lemma dgModuleFiberProjection_cycle (f : M ⟶ N) :
    (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) (dgModuleFiberProjection A D f))).val =
      dgModuleFiberProjectionElement A D f := _root_.SerrePositivity.DifferentialGraded.moduleMorphismOfCycle_cycle A D _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories
