module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PullbackNativeLiftRestriction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Kan

/-!
概要：元の native 制限を反変図式の同じ射として計算する。
方針：同じ core・宇宙持ち上げ関手の合成則を使う。
規約：制限写像を変更しない。
使われ方：局所境界比較の両射影の端点表示を小さい補題で揃える。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 元の native 制限と図式の射の合成は、同じ合成射による直接制限。 -/
lemma cocartesianPullbackNativeLiftPre_map_comp {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (q : F ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration q]
    {a b c : Over B} (f : a ⟶ b) (g : b ⟶ c) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeCoreFunctor p q) ⋙ SSet.uliftFunctor.{u + 1, u}).map g.op ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftPre p q f =
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeCoreFunctor p q) ⋙ SSet.uliftFunctor.{u + 1, u}).map (f ≫ g).op :=
  (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeCoreFunctor p q) ⋙ SSet.uliftFunctor.{u + 1, u}).map_comp
    g.op f.op).symm

/-- 同じ native core の反変図式の全ての値は、分類先の宇宙でも Kan。 -/
instance cocartesianNativeLiftCoreFunctor_obj_kan {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (q : F ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration q]
    (a : Over B) : KanComplex
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeCoreFunctor p q) ⋙
        SSet.uliftFunctor.{u + 1, u}).obj (Opposite.op a)) := by
  letI : InnerFibration (CategoryTheory.Limits.pullback.fst a.hom q) :=
    ⟨innerFibrations.pullback_fst a.hom q (InnerFibration.mem (q := q))⟩
  exact inferInstanceAs (KanComplex ((SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.cocartesianRelativeFunctorSpace (CategoryTheory.Limits.pullback.fst a.hom p)
      (CategoryTheory.Limits.pullback.fst a.hom q)) : SSet.{u})))

/-- 同じ値の core・宇宙持ち上げの表示でも Kan 性を保持する。 -/
instance cocartesianNativeLiftCore_obj_kan {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (q : F ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration q]
    (a : Over B) : KanComplex ((SSet.uliftFunctor.{u + 1, u}).obj
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeCoreFunctor p q).obj (Opposite.op a))) :=
  cocartesianNativeLiftCoreFunctor_obj_kan p q a

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
