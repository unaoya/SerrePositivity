module
public import SerrePositivity.InfinityCategories.Derived.DGModuleConeProjectionDifferential
public import SerrePositivity.DifferentialGraded.Module.ShiftUnitDifferential
public import SerrePositivity.InfinityCategories.DGNerve.Algebra

/-! # shifted cone による dg 加群の fiber 対象と射影

概要：cone(f)[−1] と閉次数零の射影、合成を零にする実原始元を構成する。
方針：shift の閉斉次単位を cone の第一・第二射影に合成する。
規約：shift の斉次単位が持つ符号を保持する。使われ方：β3 の fiber 四角形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D}

/-- 閉 dg 加群射の shifted cone としての fiber 対象。 -/
abbrev dgModuleFiber (f : M ⟶ N) : RightModule A D :=
  shiftModule (-1) (ForgetEnrichment.to (Complex A) (moduleCone A D f))

/-- shifted cone から元の始点への次数零成分。 -/
def dgModuleFiberProjectionElement (f : M ⟶ N) :
    GradedHom A (dgModuleFiber A D f) (ForgetEnrichment.to (Complex A) M) 0 :=
  compose A (moduleConeFstElement A D f)
    (moduleShiftOutElement A D (-1) (ForgetEnrichment.to (Complex A) (moduleCone A D f)))
    (by decide)

/-- 射影と元の射の合成の零ホモトピーを与える次数 −1 成分。 -/
def dgModuleFiberNullHomotopy (f : M ⟶ N) :
    GradedHom A (dgModuleFiber A D f) (ForgetEnrichment.to (Complex A) N) (-1) :=
  -compose A (moduleConeSndElement A D f)
    (moduleShiftOutElement A D (-1) (ForgetEnrichment.to (Complex A) (moduleCone A D f)))
    (by decide)

/-- shifted cone の射影成分は閉じている。 -/
lemma dgModuleFiberProjectionElement_closed (f : M ⟶ N) :
    (moduleHom A D (dgModuleFiber A D f) (ForgetEnrichment.to (Complex A) M)).d 0 1
      (dgModuleFiberProjectionElement A D f) = 0 := by
  change differential A (dgModuleFiberProjectionElement A D f) = 0
  rw [dgModuleFiberProjectionElement, differential_compose]
  have hfst : differential (D := RightModule A D) A (moduleConeFstElement A D f) = 0 :=
    moduleConeFstElement_d A D f
  have hout : differential (D := RightModule A D) A
      (moduleShiftOutElement A D (-1) (ForgetEnrichment.to (Complex A) (moduleCone A D f))) = 0 :=
    moduleShiftOutElement_d A D (-1) _
  rw [hfst, hout, zero_compose, compose_zero, smul_zero, add_zero]

/-- 全 Hom end の閉成分から得る実際の fiber 射影の閉加群射。 -/
def dgModuleFiberProjection (f : M ⟶ N) :
    ForgetEnrichment.of (Complex A) (dgModuleFiber A D f) ⟶ M :=
  moduleMorphismOfCycle A D (dgModuleFiberProjectionElement A D f)
    (dgModuleFiberProjectionElement_closed A D f)

/-- 閉加群射へ戻した射影の成分は元の指定成分。 -/
lemma dgModuleFiberProjection_cycle (f : M ⟶ N) :
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (dgModuleFiberProjection A D f))).val =
      dgModuleFiberProjectionElement A D f := moduleMorphismOfCycle_cycle A D _ _

end SerrePositivity.InfinityCategories
