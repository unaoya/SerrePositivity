module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleCofiberFiberComparisonSlice
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CofiberFiberComparisonProjection
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration

/-! # 錐比較辺の射影は明示的な比較写像

概要：slice の実際の比較辺を射影した一単体を dgModuleCofiberFiberLift の辺と同定する。
方針：join の先頭を左セルの先頭二頂点で計算し、比較単体の最初の辺を読む。
規約：端点の等式だけに依存する。使われ方：β3 の比較辺の可逆性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial

variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}

/-- 比較 join 写像の左因子への制限は明示的な比較射の辺。 -/
lemma dgModuleCofiberFiberComparisonJoin_prefix (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[1] : SSet) (SSet.horn 2 2) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberComparisonJoin A D f =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberLift A D f)).edge := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cospanJoinLeft_firstEdge, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberComparisonJoin_left,
    SSet.yonedaEquiv_symm_naturality_left]
  apply congrArg SSet.yonedaEquiv.symm
  refine (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.prepend_triangle_firstEdge _ _).trans ?_
  exact congrArg (fun c => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofEdge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pairObj (ForgetEnrichment.to (Complex A) M)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D (moduleConeInr A D f))) c)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberComparisonCycle_eq A D f)

/-- 実際の slice 比較辺を射影すると明示的比較射と同じ一単体になる。 -/
lemma dgModuleCofiberFiberComparisonSliceEdge_projection (f : M ⟶ N) :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberComparisonSliceEdge A D f).map ((SSet.truncation 2).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D (moduleConeInr A D
        f)))))).edge =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberLift A D f)).edge := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D (moduleConeInr A D
    f)))).app _
    (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverCurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberComparisonJoin A D f)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberComparisonJoin_fixed A D f))) = _
  rw [← SSet.yonedaEquiv_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceOverCurry_projection, dgModuleCofiberFiberComparisonJoin_prefix]
  exact SSet.yonedaEquiv.apply_symm_apply _

end SerrePositivity.InfinityCategories.Project.DerivedCategories
