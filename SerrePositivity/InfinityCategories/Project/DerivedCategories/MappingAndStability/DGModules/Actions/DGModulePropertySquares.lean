module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleHomotopyProperty
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGFullSquareLift
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleConePullback
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleFiberPushout

/-! # 三角的対象条件で制限した dg 加群の標準四角形

概要：K(D) の三角的条件を満たす全 dg 加群の内部で標準 cone/fiber 四角形を構成。
方針：四頂点の閉性から全単体を制限し、両普遍性を反映する。
規約：Hom end は変更しない。使われ方：ホモトピー表現可能部分の安定性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable (P : ObjectProperty (_root_.SerrePositivity.DifferentialGraded.ModuleHomotopyCategory A D))
variable [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
variable {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D} (f : M ⟶ N)
variable (hM : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyProperty A D P (ForgetEnrichment.to (Complex A) M))
variable (hN : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyProperty A D P (ForgetEnrichment.to (Complex A) N))

include hM hN

/-- 標準 cone 四角形の四頂点は同じ三角的条件を満たす。 -/
lemma dgModulePropertyConeVertices (i j : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyProperty A D P ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f) i j).obj 0) := by
  fin_cases i <;> fin_cases j
  · exact (congrArg (fun t : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) _⦋0⦌ =>
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyProperty A D P (t.obj 0))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_vertex00 A D f)).mpr (hM)
  · exact (congrArg (fun t : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) _⦋0⦌ =>
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyProperty A D P (t.obj 0))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_vertex01 A D f)).mpr (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyProperty_zero A D P)
  · exact (congrArg (fun t : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) _⦋0⦌ =>
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyProperty A D P (t.obj 0))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_vertex10 A D f)).mpr (hN)
  · exact (congrArg (fun t : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) _⦋0⦌ =>
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyProperty A D P (t.obj 0))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_vertex11 A D f)).mpr (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyProperty_cone A D P f hM hN)

/-- 標準 fiber 四角形の四頂点は同じ三角的条件を満たす。 -/
lemma dgModulePropertyFiberVertices (i j : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyProperty A D P ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D f) i j).obj 0) := by
  fin_cases i <;> fin_cases j
  · exact (congrArg (fun t : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) _⦋0⦌ =>
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyProperty A D P (t.obj 0))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare_vertex00 A D f)).mpr (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyProperty_fiber A D P f hM hN)
  · exact (congrArg (fun t : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) _⦋0⦌ =>
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyProperty A D P (t.obj 0))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare_vertex01 A D f)).mpr (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyProperty_zero A D P)
  · exact (congrArg (fun t : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) _⦋0⦌ =>
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyProperty A D P (t.obj 0))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare_vertex10 A D f)).mpr (hM)
  · exact (congrArg (fun t : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) _⦋0⦌ =>
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyProperty A D P (t.obj 0))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare_vertex11 A D f)).mpr (hN)

/-- 三角的条件を満たす加群の内部の実 cone 四角形。 -/
def dgModulePropertyConeSquare :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSquareLift A (RightModule A D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyProperty A D P)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f) (dgModulePropertyConeVertices A D P f hM hN)

/-- 三角的条件を満たす加群の内部の実 fiber 四角形。 -/
def dgModulePropertyFiberSquare :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSquareLift A (RightModule A D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyProperty A D P)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D f) (dgModulePropertyFiberVertices A D P f hM hN)

/-- 条件付き加群の cone 四角形は内部でも押し出し。 -/
lemma dgModulePropertyConeSquare_isPushout :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (dgModulePropertyConeSquare A D P f hM hN) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSquareLift_isPushout A _ _ _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_isPushout A D f)

/-- 条件付き加群の cone 四角形は内部でも引き戻し。 -/
lemma dgModulePropertyConeSquare_isPullback :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (dgModulePropertyConeSquare A D P f hM hN) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSquareLift_isPullback A _ _ _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_isPullback A D f)

/-- 条件付き加群の fiber 四角形は内部でも引き戻し。 -/
lemma dgModulePropertyFiberSquare_isPullback :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (dgModulePropertyFiberSquare A D P f hM hN) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSquareLift_isPullback A _ _ _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare_isPullback A D f)

/-- 条件付き加群の fiber 四角形は内部でも押し出し。 -/
lemma dgModulePropertyFiberSquare_isPushout :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (dgModulePropertyFiberSquare A D P f hM hN) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSquareLift_isPushout A _ _ _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare_isPushout A D f)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
