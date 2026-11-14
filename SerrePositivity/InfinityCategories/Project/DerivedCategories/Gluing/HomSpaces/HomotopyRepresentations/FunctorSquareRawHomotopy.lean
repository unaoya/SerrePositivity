module
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorTriangleSquare
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomotopyRepresentations.RelativeHomotopyEdgeClass
/-! # 合成正方形から全 path の実正方形ホモトピーへ

概要：指定三辺を持つ関手正方形を、定値 path と終側 path の間の実ホモトピーへ戻す。
方針：同じ正方形を uncurry し、結合子だけで二つの区間を並べる。
規約：四辺の全時間を保持し、正方形や path を選び直さない。
使われ方：④の指定境界充填を、⑤の入力付き path 引き戻し内の実比較へ渡す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
variable {K Z : SSet.{u}} {a b c : K ⟶ Z}
  {l : SSet.Homotopy a b} {r : SSet.Homotopy b c} {d : SSet.Homotopy a c}
  (Q : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionSquare l r d)

def dgGluingFunctorSquareRawMap : (K ⊗ (Δ[1] : SSet.{u})) ⊗ Δ[1] ⟶ Z :=
  (α_ K (Δ[1] : SSet.{u}) Δ[1]).hom ≫ uncurry Q.diagram

lemma dgGluingFunctorSquareRawMap_zero :
    (ι₀ : K ⊗ (Δ[1] : SSet.{u}) ⟶ _) ≫ dgGluingFunctorSquareRawMap Q =
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl a).h := by
  calc
    _ = uncurry ((ι₀ : (Δ[1] : SSet.{u}) ⟶ _) ≫ Q.diagram) := by
      rw [uncurry_natural_left]
      rfl
    _ = _ := by rw [Q.bottom, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]; rfl

lemma dgGluingFunctorSquareRawMap_one :
    (ι₁ : K ⊗ (Δ[1] : SSet.{u}) ⟶ _) ≫ dgGluingFunctorSquareRawMap Q = r.h := by
  calc
    _ = uncurry ((ι₁ : (Δ[1] : SSet.{u}) ⟶ _) ≫ Q.diagram) := by
      rw [uncurry_natural_left]
      rfl
    _ = _ := by rw [Q.top, uncurry_curry]

lemma dgGluingFunctorSquareRawMap_left :
    ((ι₀ : K ⟶ K ⊗ (Δ[1] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫
      dgGluingFunctorSquareRawMap Q = l.h := by
  calc
    _ = uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u}) ≫ Q.diagram) := by
      rw [uncurry_natural_left]
      rfl
    _ = _ := by rw [Q.left, uncurry_curry]

lemma dgGluingFunctorSquareRawMap_right :
    ((ι₁ : K ⟶ K ⊗ (Δ[1] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫
      dgGluingFunctorSquareRawMap Q = d.h := by
  calc
    _ = uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ Q.diagram) := by
      rw [uncurry_natural_left]
      rfl
    _ = _ := by rw [Q.right, uncurry_curry]

def dgGluingFunctorSquareRawHomotopy : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl a).h r.h where
  h := dgGluingFunctorSquareRawMap Q
  h₀ := dgGluingFunctorSquareRawMap_zero Q
  h₁ := dgGluingFunctorSquareRawMap_one Q
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro p
    exact False.elim p.1.property
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
