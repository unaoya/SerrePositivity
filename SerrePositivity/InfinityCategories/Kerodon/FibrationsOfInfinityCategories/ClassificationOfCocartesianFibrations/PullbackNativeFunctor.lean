module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PullbackHomFunctor
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PullbackNativePre

/-!
概要：両射影を底変換した元の cocartesian Hom とその core の反変関手。
方針：同じ局所 Hom との厳密な同型を使い、元の前合成の恒等・合成則を回収する。
規約：全対象・全射で元の Hom の全高次を保持する。
使われ方：底の余極限に沿う元の Hom の core の極限錐。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

variable {E F B : SSet.{u}} [Quasicategory B]
  (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (q : F ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration q]

/-- 元の各底変換の Hom の恒等射による制限は恒等。 -/
lemma cocartesianPullbackNativePre_id (a : Over B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativePre p q (𝟙 a) = 𝟙 _ := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativePre
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackHomPre_id, Category.id_comp, Iso.hom_inv_id]

/-- 元の各底変換の Hom の制限は合成順序を反転する。 -/
lemma cocartesianPullbackNativePre_comp {a b c : Over B} (f : a ⟶ b) (g : b ⟶ c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativePre p q (f ≫ g) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativePre p q g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativePre p q f := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativePre
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackHomPre_comp]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- 両射影を底変換した元の cocartesian Hom と全ての制限の反変関手。 -/
def cocartesianPullbackNativeFunctor : (Over B)ᵒᵖ ⥤ SSet.{u} where
  obj a := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.cocartesianRelativeFunctorSpace
    (pullback.fst a.unop.hom p) (pullback.fst a.unop.hom q)
  map f := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativePre p q f.unop
  map_id a := cocartesianPullbackNativePre_id p q a.unop
  map_comp f g := cocartesianPullbackNativePre_comp p q g.unop f.unop

/-- 同じ元の Hom の core と全ての制限の反変関手。 -/
def cocartesianPullbackNativeCoreFunctor : (Over B)ᵒᵖ ⥤ SSet.{u} :=
  cocartesianPullbackNativeFunctor p q ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor

/-- 元の Hom の制限図式と局所 Hom の制限図式は、同じ Hom 同型で自然に同型。 -/
def cocartesianPullbackNativeFunctorIso :
    cocartesianPullbackNativeFunctor p q ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackHomFunctor p q :=
  NatIso.ofComponents (fun a ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackHomIso p q a.unop)
    (fun f ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativePre_iso p q f.unop)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
