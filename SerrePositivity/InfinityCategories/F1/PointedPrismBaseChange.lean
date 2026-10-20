module

public import SerrePositivity.InfinityCategories.F1.FunctorParameterizedPrism
public import SerrePositivity.InfinityCategories.F1.IntervalMappingSpace
public import SerrePositivity.InfinityCategories.Core.PrismContraction

/-!
概要：パラメーター付き prism の全始域の引き戻しと射影を計算する。
方針：端点包含と因子の交換の自然性を、全次数の直積の座標で確認する。
規約：底と追加パラメーターを同時に変更する。
使われ方：完成した coslice prism を共通 weighted 始域へ制限する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- prism の端点包含は、底と追加パラメーターの同時の変更と可換。 -/
lemma prismEndpoint_tensorPrecomp {A B L M : SSet.{u}} (i : Fin 2)
    (a : A ⟶ B) (b : L ⟶ M) :
    (prismEndpoint i A ▷ L) ≫ ((Δ[1] ◁ a) ⊗ₘ b) =
      (a ⊗ₘ b) ≫ (prismEndpoint i B ▷ M) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro q
  rfl

/-- 全評価の prism は、追加 Hom パラメーターの変更と厳密に可換。 -/
lemma functorParameterizedPrism_parameterPrecomp {K B L M X : SSet.{u}}
    (b : L ⟶ M) (H : K ⊗ M ⟶ (ihom B).obj X) :
    functorParameterizedPrism ((K ◁ b) ≫ H) =
      ((K ⊗ B) ◁ b) ≫ functorParameterizedPrism H := by
  rw [functorParameterizedPrism, uncurry_natural_left, functorParameterizedPrism]
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

end SerrePositivity.InfinityCategories
