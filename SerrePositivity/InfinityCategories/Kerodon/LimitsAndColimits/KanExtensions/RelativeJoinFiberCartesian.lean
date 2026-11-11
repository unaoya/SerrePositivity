module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeRestrictionCartesianFibration
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinCoconeFiber

/-!
概要：相対 join の関手の族の制限は、各底の fiber で cartesian fibration。
方針：fiber の可換な同型で通常の余錐制限の cartesian 輸送を移す。
規約：元の構造射 p の fibration 性は不要。
使われ方：制限 V 自体の cartesian 性の fiber の入力。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：同型で結ばれた可換四角形に沿って cartesian fibration 性を移せる。
方針：新しい射を始域同型の逆、元の射、終域同型の合成に分解する。
規約：両同型の向きは元の射から新しい射へ。
使われ方：fiber の表示を通常の余錐制限から関手の族へ移す。 -/
lemma kanCartesianFibration_of_iso_square {E B E' B' : SSet.{u}}
    (p : E ⟶ B) (p' : E' ⟶ B') [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration p]
    (e : E ≅ E') (b : B ≅ B') (h : e.hom ≫ p' = p ≫ b.hom) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration p' := by
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration e.inv := ⟨MorphismProperty.of_isIso _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightFibrations e.inv⟩
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration b.hom := ⟨MorphismProperty.of_isIso _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightFibrations b.hom⟩
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration (e.inv ≫ p ≫ b.hom) := inferInstance
  have hp' : e.inv ≫ p ≫ b.hom = p' := by
    rw [← h, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  rw [hp'] at hc
  exact hc

/-- 概要：相対 join の制限は各底の頂点の fiber で cartesian fibration。
方針：fiber の表示と通常の余錐の関手空間の同型の可換性を使う。
規約：値域 D は quasicategory、p と底 C は任意。
使われ方：inner fibration かつ輸送を保つ V の cartesian 性への fiber の入力。 -/
lemma kanRelativeJoinRestrictionFiber_cartesianFibration {K C D : SSet.{u}}
    [Quasicategory D] (p : K ⟶ C) (c : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHomPreFiber (D := D) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinInlOver p) c) := by
  exact kanCartesianFibration_of_iso_square (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p c) D) _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinCoconeFiberIso p c D) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.fiberwiseHomFiberIso p c D)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinCoconeFiberIso_restriction p c)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
