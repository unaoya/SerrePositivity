module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PullbackNativeCoreDescent
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PullbackNativeFunctor

/-!
概要：底を覆う余極限に対する、元の全 cocartesian Hom の core の制限錐は極限。
方針：同じ底変換への制限を脚とし、全パラメーターの族の回収と一意性を束ねる。
規約：局所の Hom は両射影を底変換した元の cocartesian 相対 Hom。
使われ方：分類主写像の元の Hom 比較を、底のセルに沿って貼り合わせる。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

variable {J : Type v} [Category.{w} J]
  {E F B : SSet.{u}} [Quasicategory B]
  (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (q : F ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration q]
  (D : J ⥤ Over B)

/-- 大域の元の cocartesian Hom の core から、各底変換の元の Hom の core への制限錐。 -/
def cocartesianPullbackNativeCoreCone :
    Cone (D.op ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeCoreFunctor p q) where
  pt := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.cocartesianRelativeFunctorSpace p q) : SSet.{u})
  π :=
    { app := fun j ↦
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeRestriction p q (D.obj j.unop))
      naturality := by
        intro j k f
        change 𝟙 _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.map _ =
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.map _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.map _
        rw [Category.id_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.map_comp]
        exact congrArg (fun h ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.map h)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeRestriction_naturality p q (D.map f.unop)).symm }

/-- 錐の自然性は、元の各底変換の Hom の core の族の整合性そのもの。 -/
lemma cocartesianPullbackNativeCoreCone_compatible
    (s : Cone (D.op ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeCoreFunctor p q))
    {j k : J} (f : j ⟶ k) :
    s.π.app (Opposite.op j) = s.π.app (Opposite.op k) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativePre p q (D.map f)) :=
  (s.w f.op).symm

/-- 底を覆う余極限から得た元の Hom の core の制限錐は、実際の極限錐。 -/
def cocartesianPullbackNativeCoreCone_isLimit [Small.{u} J]
    (hc : IsColimit ((Over.forgetCocone B).whisker D)) :
    IsLimit (cocartesianPullbackNativeCoreCone p q D) where
  lift s := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeCoreColimitLift p q D hc
    (fun j ↦ s.π.app (Opposite.op j)) (cocartesianPullbackNativeCoreCone_compatible p q D s)
  fac s j := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeCoreColimitLift_fac p q D hc _ _ j.unop
  uniq s m hm := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeCoreColimitLift_unique p q D hc
      (fun j ↦ s.π.app (Opposite.op j))
      (cocartesianPullbackNativeCoreCone_compatible p q D s) m
    intro j
    exact hm (Opposite.op j)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
