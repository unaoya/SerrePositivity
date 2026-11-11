module

public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.CompositionTriangleSpace

/-!
概要：元の二辺を固定した全パラメーターの三角形を、同じ延長空間の族として読む。
方針：内部 Hom の curry と固定 fiber の普遍性で両方向を構成する。
規約：底の二辺と三角形そのものを保持する。
使われ方：実際の正方形から取り出した合成三角形を、可縮な比較先へ写す。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 同じ内ホーン上で固定した三角形の全パラメーターの族を延長空間に戻す。 -/
def innerTriangleExtensionCurry {T X : SSet.{u}} (a : (horn 2 1 : SSet.{u}) ⟶ X)
    (H : (Δ[2] : SSet.{u}) ⊗ T ⟶ X)
    (h : ((horn 2 1).ι ▷ T) ≫ H = fst (horn 2 1 : SSet.{u}) T ≫ a) :
    T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.innerTriangleExtensionSpace a :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift _ _ (curry H) (by
    apply uncurry_injective
    rw [uncurry_pre_app, uncurry_curry, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]
    exact h)

/-- 同じ延長空間の族を、元の全パラメーターの三角形として評価する。 -/
def innerTriangleExtensionUncurry {T X : SSet.{u}} {a : (horn 2 1 : SSet.{u}) ⟶ X}
    (f : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.innerTriangleExtensionSpace a) : (Δ[2] : SSet.{u}) ⊗ T ⟶ X :=
  uncurry (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((pre (horn 2 1).ι).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a))

/-- 同じ三角形を延長空間の族へ戻して展開すると、元の三角形そのもの。 -/
lemma innerTriangleExtensionUncurry_curry {T X : SSet.{u}} (a : (horn 2 1 : SSet.{u}) ⟶ X)
    (H : (Δ[2] : SSet.{u}) ⊗ T ⟶ X)
    (h : ((horn 2 1).ι ▷ T) ≫ H = fst (horn 2 1 : SSet.{u}) T ≫ a) :
    innerTriangleExtensionUncurry (innerTriangleExtensionCurry a H h) = H := by
  unfold innerTriangleExtensionUncurry innerTriangleExtensionCurry
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, uncurry_curry]

/-- 同じ延長空間の族は、元の三角形への全パラメーターの展開で一意に決まる。 -/
lemma innerTriangleExtensionUncurry_injective {T X : SSet.{u}}
    (a : (horn 2 1 : SSet.{u}) ⟶ X) :
    Function.Injective (innerTriangleExtensionUncurry (T := T) (a := a)) := by
  intro f g h
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext ((pre (horn 2 1).ι).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)
  exact uncurry_injective h

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
