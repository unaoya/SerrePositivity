module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.TrivialFibrationEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitCoconeRestriction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceRestriction
public import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct

/-!
概要：分裂三角形を、指定した元の余錐の恒等長辺を保って持ち上げる。
方針：全単射に対する持ち上げ性を、三角形の長辺包含に適用する。
規約：長辺を恒等辺として固定し、両端の元の余錐を同時に保持する。
使われ方：偶数前置図式で選んだ因子化を、元の全交互前置図式へ延長する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：元の恒等長辺を保つ三角形の全持ち上げ。
方針：δ₁ の単射に対する trivial Kan 持ち上げを使う。
規約：元の三角形の像と長辺の双方を厳密に保つ。
使われ方：指定増大余錐を変えない分裂比較の延長。 -/
lemma exists_splitTriangle_lift {X Y : SSet.{u}} (p : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p]
    (x : X _⦋0⦌) (T : Y _⦋2⦌)
    (hT : Y.δ 1 T = (SSet.Edge.id (p.app _ x)).edge) :
    ∃ S : X _⦋2⦌, p.app _ S = T ∧ X.δ 1 S = (SSet.Edge.id x).edge := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := p) (SSet.stdSimplex.δ (1 : Fin 3)) inferInstance
  have sq : CommSq (SSet.yonedaEquiv.symm (SSet.Edge.id x).edge)
      (SSet.stdSimplex.δ (1 : Fin 3)) p (SSet.yonedaEquiv.symm T) := by
    constructor
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply,
      SSet.stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply, hT]
    exact congrArg SSet.Edge.edge (SSet.Edge.map_id x p)
  refine ⟨SSet.yonedaEquiv sq.lift, ?_, ?_⟩
  · rw [← SSet.yonedaEquiv_comp, sq.fac_right, Equiv.apply_symm_apply]
  · rw [← SSet.stdSimplex.yonedaEquiv_δ_comp, sq.fac_left, Equiv.apply_symm_apply]

/-- 概要：前置部分での分裂三角形は、元の全余錐を恒等長辺に保って延長できる。
方針：right anodyne 制限の trivial Kan 性に全三角形の持ち上げを適用する。
規約：二つの端の余錐を別々に選ばず、同じ元の余錐に固定する。
使われ方：可算交互構成の有限前置図式を保つ延長。 -/
lemma exists_relativeCoslice_splitTriangle {K L C : SSet.{u}} [Quasicategory C]
    (j : K ⟶ L) [Mono j] (hj : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions j)
    (F : L ⟶ C) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F) (T : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (j ≫ F)) _⦋2⦌)
    (hT : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (j ≫ F)).δ 1 T = (SSet.Edge.id (c.restrict j)).edge) :
    ∃ S : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F) _⦋2⦌,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict F j).app _ S = T ∧
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F).δ 1 S = (SSet.Edge.id c).edge := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict_trivialKanFibration F j hj
  exact exists_splitTriangle_lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict F j) c T hT

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
