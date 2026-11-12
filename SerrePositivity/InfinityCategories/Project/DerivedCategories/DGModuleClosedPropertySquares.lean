module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFullSquareLift
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleConePullback
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFiberPushout

/-!
概要：零・標準 cone・fiber で閉じる dg 加群の条件を、実四角形へ制限する。
方針：四頂点の閉性と充満包含への全単体の持ち上げを使う。
規約：ホモトピー同型での replete 性を要求しない。使われ方：β5 の射影的加群。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
/-- 零・標準 cone・標準 fiber で閉じる、実 dg 加群の対象条件。 -/
structure DGModuleClosedProperty (P : _root_.SerrePositivity.DifferentialGraded.RightModule A D → Prop) : Prop where
  zero : P (_root_.SerrePositivity.DifferentialGraded.zeroModule A D)
  cone {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D} (f : M ⟶ N) :
    P (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M) → P (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) N) →
      P (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f))
  fiber {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D} (f : M ⟶ N) :
    P (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M) → P (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) N) →
      P (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f)
variable (P : _root_.SerrePositivity.DifferentialGraded.RightModule A D → Prop) (hP : DGModuleClosedProperty A D P)
variable {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D} (f : M ⟶ N)
variable (hM : P (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M))
variable (hN : P (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) N))

include hP hM hN

/-- 標準 cone 四角形の四頂点は同じ三角的条件を満たす。 -/
lemma dgClosedModuleConeVertices (i j : Fin 2) :
    P ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f) i j).obj 0) := by
  fin_cases i <;> fin_cases j
  · exact (congrArg (fun t : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) _⦋0⦌ =>
      P (t.obj 0))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_vertex00 A D f)).mpr (hM)
  · exact (congrArg (fun t : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) _⦋0⦌ =>
      P (t.obj 0))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_vertex01 A D f)).mpr (hP.zero)
  · exact (congrArg (fun t : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) _⦋0⦌ =>
      P (t.obj 0))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_vertex10 A D f)).mpr (hN)
  · exact (congrArg (fun t : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) _⦋0⦌ =>
      P (t.obj 0))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_vertex11 A D f)).mpr (hP.cone f hM hN)

/-- 標準 fiber 四角形の四頂点は同じ三角的条件を満たす。 -/
lemma dgClosedModuleFiberVertices (i j : Fin 2) :
    P ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D f) i j).obj 0) := by
  fin_cases i <;> fin_cases j
  · exact (congrArg (fun t : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) _⦋0⦌ =>
      P (t.obj 0))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare_vertex00 A D f)).mpr (hP.fiber f hM hN)
  · exact (congrArg (fun t : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) _⦋0⦌ =>
      P (t.obj 0))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare_vertex01 A D f)).mpr (hP.zero)
  · exact (congrArg (fun t : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) _⦋0⦌ =>
      P (t.obj 0))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare_vertex10 A D f)).mpr (hM)
  · exact (congrArg (fun t : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) _⦋0⦌ =>
      P (t.obj 0))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare_vertex11 A D f)).mpr (hN)

/-- 三角的条件を満たす加群の内部の実 cone 四角形。 -/
def dgClosedModuleConeSquare :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSquareLift A (RightModule A D) (P)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f) (dgClosedModuleConeVertices A D P hP f hM hN)

/-- 三角的条件を満たす加群の内部の実 fiber 四角形。 -/
def dgClosedModuleFiberSquare :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSquareLift A (RightModule A D) (P)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D f) (dgClosedModuleFiberVertices A D P hP f hM hN)

/-- 条件付き加群の cone 四角形は内部でも押し出し。 -/
lemma dgClosedModuleConeSquare_isPushout :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (dgClosedModuleConeSquare A D P hP f hM hN) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSquareLift_isPushout A _ _ _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_isPushout A D f)

/-- 条件付き加群の cone 四角形は内部でも引き戻し。 -/
lemma dgClosedModuleConeSquare_isPullback :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (dgClosedModuleConeSquare A D P hP f hM hN) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSquareLift_isPullback A _ _ _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_isPullback A D f)

/-- 条件付き加群の fiber 四角形は内部でも引き戻し。 -/
lemma dgClosedModuleFiberSquare_isPullback :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (dgClosedModuleFiberSquare A D P hP f hM hN) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSquareLift_isPullback A _ _ _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare_isPullback A D f)

/-- 条件付き加群の fiber 四角形は内部でも押し出し。 -/
lemma dgClosedModuleFiberSquare_isPushout :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (dgClosedModuleFiberSquare A D P hP f hM hN) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSquareLift_isPushout A _ _ _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare_isPushout A D f)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
