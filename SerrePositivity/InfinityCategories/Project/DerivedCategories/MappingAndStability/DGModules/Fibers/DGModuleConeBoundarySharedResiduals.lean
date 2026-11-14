module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleConeBoundaryResiduals
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SpanPresentations.SpanSharedRhs

/-! # 共通の cochain 右辺と右側境界データの比較

概要：後続・A 側の右辺を一度だけ cochain に移し、右側の生の右辺とも異種等号で比較する。
方針：左側の移送の異種等号に、共通面からの左右の異種等号を合成する。
規約：最初の頂点に標準 cofiber 余錐を指定する。使われ方：D7 の二つの共通残差。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Opposite DifferentialGraded CochainComplex HomComplex
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}

/-- 概要：cochain 座標の r_0 は右側データの生の右辺と異種等号で一致する。
方針：左側の移送の異種等号と左右の共通右辺の比較を合成する。
規約：右側の移送を選び直さない。使われ方：右セルの微分条件の移送。 -/
lemma dgModuleConeBoundaryRhs0_heq_right {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f)) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhs0 A D f b hb) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRightBase A D f
      b).spanSuffixRhs) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhs0_heq A D f b hb).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryZeroData_suffixRhs_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b))

/-- 概要：cochain 座標の r_A は右側データの生の右辺と異種等号で一致する。
方針：左側の移送の異種等号と左右の共通右辺の比較を合成する。
規約：右側の移送を選び直さない。使われ方：右セルの微分条件の移送。 -/
lemma dgModuleConeBoundaryRhsA_heq_right {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f)) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsA A D f b hb)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRightBase A D f b).spanOnePrefixRhs 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsA_heq A D f b hb).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryZeroData_A_rhs_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
