module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.HornBoundaryDiagramPullbacks

/-!
概要：元の全 native Hom の大域制限を、同じ反変図式の値へ端点を揃えて写す。
方針：一般の底上の対象のまま端点を正規化し、元の厳密な自然性を移す。
規約：元の全 Hom と同じ制限写像を保持する。
使われ方：境界比較の大域 Hom への前合成と両射影の計算。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
variable {E F B : SSet.{u}} [Quasicategory B]
  (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (q : F ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration q]

/-- 元の大域 native 制限を、同じ反変図式の端点へ揃えた射。 -/
def cocartesianNativeGlobalDiagramRestriction (a : Over B) :
    (SSet.uliftFunctor.{u + 1, u}).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.cocartesianRelativeFunctorSpace p q) : SSet.{u}) ⟶
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftCoreFunctor p q).obj (Opposite.op a) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftRestriction p q a

/-- 同じ端点表示の射は、元の制限そのもの。 -/
lemma cocartesianNativeGlobalDiagramRestriction_eq (a : Over B) :
    cocartesianNativeGlobalDiagramRestriction p q a =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftRestriction p q a := rfl

/-- 同じ端点表示でも、大域制限は底上の射に厳密に自然。 -/
lemma cocartesianNativeGlobalDiagramRestriction_naturality {a b : Over B} (f : a ⟶ b) :
    cocartesianNativeGlobalDiagramRestriction p q b ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftCoreFunctor p q).map f.op =
    cocartesianNativeGlobalDiagramRestriction p q a := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftRestriction_naturality p q f
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftPre_eq_diagramMap] at h
  dsimp only [cocartesianNativeGlobalDiagramRestriction,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftCoreFunctor, Functor.comp_obj, Functor.comp_map,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeCoreFunctor, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeFunctor,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor] at h ⊢
  exact h

/-- 分類先の大域制限も、同じ反変図式の端点へ揃えて表示する。 -/
def intervalDiagramGlobalDiagramRestriction {B₀ : SSet.{u}} {X : SSet.{u + 1}}
    (P Q : (SSet.uliftFunctor.{u + 1, u}).obj B₀ ⟶ X) (a : Over B₀) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex P) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex Q) ⟶
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.intervalDiagramLiftOverFunctor P Q).obj (Opposite.op a) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramRestriction ((SSet.uliftFunctor.{u + 1, u}).map a.hom) P Q

/-- 同じ分類先の大域制限も、底上の射に厳密に自然。 -/
lemma intervalDiagramGlobalDiagramRestriction_naturality {B₀ : SSet.{u}} {X : SSet.{u + 1}}
    (P Q : (SSet.uliftFunctor.{u + 1, u}).obj B₀ ⟶ X) {a b : Over B₀} (f : a ⟶ b) :
    intervalDiagramGlobalDiagramRestriction P Q b ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.intervalDiagramLiftOverFunctor P Q).map f.op =
    intervalDiagramGlobalDiagramRestriction P Q a := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramOverPre_restriction P Q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.uliftOverMorphism f)
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.intervalDiagramOverPre_ulift_eq_diagramMap] at h
  dsimp only [intervalDiagramGlobalDiagramRestriction, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.intervalDiagramLiftOverFunctor]
  exact h

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
