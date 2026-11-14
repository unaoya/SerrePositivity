module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.CofiberBoundaryResiduals
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SpanPresentations.SpanSharedRhs

/-! # 共通の cochain 右辺と右側境界データの比較

概要：後続・A 側の右辺を一度だけ cochain に移し、右側の生の右辺とも異種等号で比較する。
方針：左側の移送の異種等号に、共通面からの左右の異種等号を合成する。
規約：最初の頂点に標準 cofiber 余錐を指定する。使われ方：D7 の二つの共通残差。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Opposite DifferentialGraded CochainComplex HomComplex
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S] {A B C : _root_.SerrePositivity.DifferentialGraded.Complex S}

/-- 概要：cochain 座標の r_0 は右側データの生の右辺と異種等号で一致する。
方針：左側の移送の異種等号と左右の共通右辺の比較を合成する。
規約：右側の移送を選び直さない。使われ方：右セルの微分条件の移送。 -/
lemma cofiberBoundaryRhs0_heq_right {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberCocone f g)) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhs0 f g b hb) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightBase f g b).spanSuffixRhs) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhs0_heq f g b hb).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryZeroData_suffixRhs_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b))

/-- 概要：cochain 座標の r_A は右側データの生の右辺と異種等号で一致する。
方針：左側の移送の異種等号と左右の共通右辺の比較を合成する。
規約：右側の移送を選び直さない。使われ方：右セルの微分条件の移送。 -/
lemma cofiberBoundaryRhsA_heq_right {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberCocone f g)) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsA f g b hb)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightBase f g b).spanOnePrefixRhs 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsA_heq f g b hb).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryZeroData_A_rhs_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
