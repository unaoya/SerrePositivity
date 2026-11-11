module
public import SerrePositivity.KST.SConstruction.DGModuleClosedOperations
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFullSquareLift
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleConePullback
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFiberPushout

/-! # 実有限操作の閉性で制限した dg 加群の標準四角形

概要：K(D) の実操作の条件を満たす全 dg 加群の内部で標準 cone/fiber 四角形を構成。
方針：四頂点の閉性から全単体を制限し、両普遍性を反映する。
規約：Hom end は変更しない。使われ方：ホモトピー表現可能部分の安定性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable (P : _root_.SerrePositivity.DifferentialGraded.RightModule A D → Prop) (hP : DGModuleClosedOperations A D P)
variable {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D} (f : M ⟶ N)
variable (hM : P (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M))
variable (hN : P (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) N))

include hM hN hP

/-- 標準 cone 四角形の四頂点は同じ実操作の条件を満たす。 -/
lemma dgModuleClosedConeVertices (i j : Fin 2) :
    P ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f) i j).obj 0) := by
  fin_cases i <;> fin_cases j
  · exact (congrArg (fun t : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) _⦋0⦌ =>
      P (t.obj 0))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_vertex00 A D f)).mpr (hM)
  · exact (congrArg (fun t : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) _⦋0⦌ =>
      P (t.obj 0))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_vertex01 A D f)).mpr (hP.zero_mem)
  · exact (congrArg (fun t : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) _⦋0⦌ =>
      P (t.obj 0))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_vertex10 A D f)).mpr (hN)
  · exact (congrArg (fun t : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) _⦋0⦌ =>
      P (t.obj 0))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_vertex11 A D f)).mpr (hP.cone_mem f hM hN)

/-- 標準 fiber 四角形の四頂点は同じ実操作の条件を満たす。 -/
lemma dgModuleClosedFiberVertices (i j : Fin 2) :
    P ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D f) i j).obj 0) := by
  fin_cases i <;> fin_cases j
  · exact (congrArg (fun t : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) _⦋0⦌ =>
      P (t.obj 0))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare_vertex00 A D f)).mpr (hP.fiber_mem f hM hN)
  · exact (congrArg (fun t : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) _⦋0⦌ =>
      P (t.obj 0))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare_vertex01 A D f)).mpr (hP.zero_mem)
  · exact (congrArg (fun t : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) _⦋0⦌ =>
      P (t.obj 0))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare_vertex10 A D f)).mpr (hM)
  · exact (congrArg (fun t : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) _⦋0⦌ =>
      P (t.obj 0))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare_vertex11 A D f)).mpr (hN)

/-- 実操作の条件を満たす加群の内部の実 cone 四角形。 -/
def dgModuleClosedConeSquare :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSquareLift A (RightModule A D) (P)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f) (dgModuleClosedConeVertices A D P hP f hM hN)

/-- 実操作の条件を満たす加群の内部の実 fiber 四角形。 -/
def dgModuleClosedFiberSquare :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSquareLift A (RightModule A D) (P)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D f) (dgModuleClosedFiberVertices A D P hP f hM hN)

/-- 条件付き加群の cone 四角形は内部でも押し出し。 -/
lemma dgModuleClosedConeSquare_isPushout :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (dgModuleClosedConeSquare A D P hP f hM hN) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSquareLift_isPushout A _ _ _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_isPushout A D f)

/-- 条件付き加群の cone 四角形は内部でも引き戻し。 -/
lemma dgModuleClosedConeSquare_isPullback :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (dgModuleClosedConeSquare A D P hP f hM hN) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSquareLift_isPullback A _ _ _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_isPullback A D f)

/-- 条件付き加群の fiber 四角形は内部でも引き戻し。 -/
lemma dgModuleClosedFiberSquare_isPullback :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (dgModuleClosedFiberSquare A D P hP f hM hN) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSquareLift_isPullback A _ _ _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare_isPullback A D f)

/-- 条件付き加群の fiber 四角形は内部でも押し出し。 -/
lemma dgModuleClosedFiberSquare_isPushout :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (dgModuleClosedFiberSquare A D P hP f hM hN) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSquareLift_isPushout A _ _ _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare_isPushout A D f)

end SerrePositivity.KST.SConstruction
