module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinPullbackCocartesian

/-!
概要：相対 join 上の可逆化する図式の制限は、元の図式の族の cartesian 辺になる。
方針：底変換した左包含の cocartesian 辺の保存と curry の自然性を使う。
規約：底への射は区間上で固定し、全ての等式を厳密に扱う。
使われ方：普遍余錐の制限の全空間での輸送。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：底上の射による図式の制限は相対指数の curry と可換。
方針：局所形の自然変換に対する一般の自然性を使う。
規約：底上の対象もパラメータも任意。
使われ方：可逆化する図式の制限を相対指数の辺へ移す。 -/
lemma kanFiberwiseHomCurry_pre {C D A : SSet.{u}} {K L : Over C} (i : K ⟶ L)
    (b : A ⟶ C) (H : pullback b L.hom ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomCurry K.hom b (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackMap i (Over.mk b) ≫ H) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomCurry L.hom b H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomPre i :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseFunctorCurry_pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackMapNat i) ⟨b, H⟩

/-- 概要：相対 join 上の可逆化する区間の図式を制限すると元の相対指数の cartesian 辺になる。
方針：左包含の底変換が cocartesian 辺を保存することを可逆化条件に渡す。
規約：元の射 p は cocartesian fibration、値域 D は quasicategory。
使われ方：相対 join の関手の族の特殊な輸送が制限と両立することの確認。 -/
lemma kanRelativeJoinCurry_pre_isCartesianEdge {K C D : SSet.{u}}
    (p : K ⟶ C) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] [Quasicategory D]
    (b : (Δ[1] : SSet.{u}) ⟶ C)
    (H : pullback b (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection p (𝟙 C)) ⟶ D)
    (hH : ∀ s : (pullback b (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection p (𝟙 C))) _⦋1⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (pullback.fst b (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection p (𝟙 C))) s →
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (H.app (Opposite.op ⦋1⦌) s))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomProjection p D)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomPre (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinInlOver p)).app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomCurry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection p (𝟙 C)) b H))) := by
  rw [← SSet.yonedaEquiv_comp]
  erw [← kanFiberwiseHomCurry_pre (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinInlOver p) b H]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHom_isCartesianEdge_of_inverting
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHomInvertingEdge_of_diagram
  intro s hs
  exact hH _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinInl_overPullback_preservesCocartesian p b s hs)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
