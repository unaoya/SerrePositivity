module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.Reflection

/-!
概要：持ち上げた Kan 複体間の同値を元の宇宙へ戻す。
方針：同値の順方向の射を降ろし、同値性の反映で小さい同値データを得る。
規約：降ろした射そのものを順方向に固定する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、小さい unstraightening の fiber と図式の値の比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：持ち上げた単体集合間の射を降ろして再び持ち上げると元の射になる。
方針：各次数の入力と出力の ULift の往復を計算する。
規約：射が元の宇宙から来たという仮定は不要。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、選択済みの大きい比較射を小さい宇宙へ戻す。 -/
lemma uliftMorphismDown_lift {X Y : SSet.{u}}
    (f : (SSet.uliftFunctor.{v, u}).obj X ⟶ (SSet.uliftFunctor.{v, u}).obj Y) :
    (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftMorphismDown f) = f := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨x⟩
  rfl

/-- 概要：持ち上げた Kan 複体間の同値を元の Kan 複体間の同値へ降ろす。
方針：順方向の射を降ろし、持ち上げによる同値性の反映を使う。
規約：逆射は降ろした順方向の射の同値性から選ぶ。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、fiber の比較を元の空間の宇宙で得る。 -/
noncomputable def QCatEquivalence.downOfKan {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((SSet.uliftFunctor.{v, u}).obj X)
      ((SSet.uliftFunctor.{v, u}).obj Y)) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X Y :=
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.isQCatEquivalence_ulift_iff_of_kan (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftMorphismDown e.hom)).mp
    (by rw [uliftMorphismDown_lift]; exact e.isQCatEquivalence)).choose

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.QCatEquivalence (downOfKan)


end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
