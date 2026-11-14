module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.FirstUnitCollarFamilies
/-! # 区間と単体パラメーターの再添字を元入力へ拡張する

概要：有限幾何の prism 再添字を元入力全体へ拡張し、面・端点退化を保持する。
方針：入力因子をそのまま保ち、結合子と右 tensor だけで輸送する。
規約：辺変数・単体パラメーター・元入力を変更しない。
使われ方：係数側の六つの三角形の共有辺と端点固定を導来四面体へ移す。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

def dgGluingPrismParameterReindex {A B : SSet.{u}}
    (W : (Δ[1] : SSet.{u}) ⊗ A ⟶ Δ[1] ⊗ B) (K : SSet.{u}) :
    (Δ[1] : SSet.{u}) ⊗ (A ⊗ K) ⟶ Δ[1] ⊗ (B ⊗ K) :=
  (α_ (Δ[1] : SSet.{u}) A K).inv ≫ (W ▷ K) ≫ (α_ (Δ[1] : SSet.{u}) B K).hom

lemma dgGluingPrismParameterReindex_pre {A A' B : SSet.{u}}
    (W : (Δ[1] : SSet.{u}) ⊗ A ⟶ Δ[1] ⊗ B) (K : SSet.{u}) (f : A' ⟶ A) :
    (Δ[1] ◁ (f ▷ K)) ≫ dgGluingPrismParameterReindex W K =
      dgGluingPrismParameterReindex ((Δ[1] ◁ f) ≫ W) K := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl

lemma dgGluingPrismParameterReindex_endpoint_retract {A A' B : SSet.{u}}
    (W : (Δ[1] : SSet.{u}) ⊗ A ⟶ Δ[1] ⊗ B)
    (W' : (Δ[1] : SSet.{u}) ⊗ A' ⟶ Δ[1] ⊗ B) (K : SSet.{u})
    (i : Fin 2) (f : A ⟶ A')
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i A ≫ W = f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i A' ≫ W') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i (A ⊗ K) ≫ dgGluingPrismParameterReindex W K =
      (f ▷ K) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i (A' ⊗ K) ≫ dgGluingPrismParameterReindex W' K := by
  calc
    _ = ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i A ≫ W) ▷ K) ≫ (α_ (Δ[1] : SSet.{u}) B K).hom := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl
    _ = ((f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i A' ≫ W') ▷ K) ≫
        (α_ (Δ[1] : SSet.{u}) B K).hom := by rw [h]
    _ = _ := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl

lemma dgGluingPrismParameterReindex_triangle_diagonal {A B K : SSet.{u}}
    (W : A ⊗ (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ B) (d : (Δ[1] : SSet.{u}) ⟶ A) :
    dgGluingPrismParameterReindex ((d ▷ Δ[1]) ≫ W) K =
      (Δ[1] ◁ (β_ (Δ[1] : SSet.{u}) K).hom) ≫
        (d ▷ (K ⊗ Δ[1])) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleTimeReindex W := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl

lemma dgGluingPrismParameterReindex_post {A B B' : SSet.{u}}
    (W : (Δ[1] : SSet.{u}) ⊗ A ⟶ Δ[1] ⊗ B) (K : SSet.{u}) (f : B ⟶ B') :
    dgGluingPrismParameterReindex (W ≫ (Δ[1] ◁ f)) K =
      dgGluingPrismParameterReindex W K ≫ (Δ[1] ◁ (f ▷ K)) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
