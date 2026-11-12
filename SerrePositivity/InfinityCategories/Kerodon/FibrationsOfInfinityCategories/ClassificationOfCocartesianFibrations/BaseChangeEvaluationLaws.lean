module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictTransportBaseChange
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PullbackNativeRestriction

/-!
概要：元の底変換比較と全相対 Hom の制限を、各次数の評価で展開する。
方針：全パラメーターの展開の射影公式を、同じ次数の指定単体で評価する。
規約：零単体だけでなく任意の次数の全パラメーターを保持する。
使われ方：strict transport の底変換比較と元の全相対 Hom の作用の可換式。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 元の strict transport の底変換成分は、元の全空間への評価後に under の制限となる。 -/
lemma cocartesianStrictTransportBaseChangeComponent_apply_snd
    {C D : Type u} [Category.{u} C] [Category.{u} D] {E : SSet.{u}}
    (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (k : D ⥤ C) (d : D)
    {n : SimplexCategoryᵒᵖ} (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransport p (k.obj d)).obj n)
    (x : (nerve (Under d)).obj n) :
    (pullback.snd (nerveMap k) p).app n
      ((((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportBaseChangeComponent p k d).app n s).val.val.app n (𝟙 n)) x) =
    s.val.val.app n (𝟙 n) ((nerveMap (Under.post k)).app n x) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportBaseChangeComponent_uncurry_snd p k d
    (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransport p (k.obj d)))
  exact congrArg (fun z ↦ z.app n (x, s)) h

/-- 元の全相対 Hom の底変換は、元の全空間への評価後に元の関手の評価となる。 -/
lemma cocartesianPullbackNativeRestriction_apply_snd
    {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (q : F ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration q] (a : Over B)
    {n : SimplexCategoryᵒᵖ} (h : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.cocartesianRelativeFunctorSpace p q).obj n)
    (x : (pullback a.hom p).obj n) :
    (pullback.snd a.hom q).app n
      ((((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeRestriction p q a).app n h).val.val.app n (𝟙 n)) x) =
    h.val.val.app n (𝟙 n) ((pullback.snd a.hom p).app n x) := by
  have hr := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeRestriction_uncurry_snd p q a
    (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.cocartesianRelativeFunctorSpace p q))
  exact congrArg (fun z ↦ z.app n (x, h)) hr

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
