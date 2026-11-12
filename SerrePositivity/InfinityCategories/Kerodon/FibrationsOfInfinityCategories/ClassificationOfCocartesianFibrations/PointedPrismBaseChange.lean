module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorParameterizedPrism
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingSpace
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction

/-!
概要：パラメーター付き prism の全始域の引き戻しと射影を計算する。
方針：端点包含と因子の交換の自然性を、全次数の直積の座標で確認する。
規約：底と追加パラメーターを同時に変更する。
使われ方：完成した coslice prism を共通 weighted 始域へ制限する。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- prism の端点包含は、底と追加パラメーターの同時の変更と可換。 -/
lemma prismEndpoint_tensorPrecomp {A B L M : SSet.{u}} (i : Fin 2)
    (a : A ⟶ B) (b : L ⟶ M) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i A ▷ L) ≫ ((Δ[1] ◁ a) ⊗ₘ b) =
      (a ⊗ₘ b) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i B ▷ M) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro q
  rfl

/-- 全評価の prism は、追加 Hom パラメーターの変更と厳密に可換。 -/
lemma functorParameterizedPrism_parameterPrecomp {K B L M X : SSet.{u}}
    (b : L ⟶ M) (H : K ⊗ M ⟶ (ihom B).obj X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorParameterizedPrism ((K ◁ b) ≫ H) =
      ((K ⊗ B) ◁ b) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorParameterizedPrism H := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorParameterizedPrism, uncurry_natural_left, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorParameterizedPrism]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro q
  rfl

/-- 底の係数射影は、二つのパラメーター変更の後でも同じ底と Hom パラメーターを保つ。 -/
lemma prismCoefficientProjection_tensorPrecomp {A B C L M : SSet.{u}}
    (a : A ⟶ B) (q : B ⟶ C) (b : L ⟶ M) :
    ((Δ[1] ◁ a) ⊗ₘ b) ≫ ((Δ[1] ◁ q) ▷ M) =
      ((Δ[1] ◁ (a ≫ q)) ▷ L) ≫ ((Δ[1] ⊗ C) ◁ b) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro z
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
