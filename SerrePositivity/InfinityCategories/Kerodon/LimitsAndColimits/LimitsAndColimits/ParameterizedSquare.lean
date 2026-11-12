module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Square
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
概要：全パラメーターを保った正方形の、同じ対角に沿う三角形の貼り合わせ。
方針：二三角形の pushout をテンソルの右因子で移し、その普遍性を使う。
規約：元の三角形とその高次パラメーターを変更しない。
使われ方：分類先の固定成分 Hom の正方形を、二つの実際の三角形へ分解する。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 正方形の同じ二三角形の分解は、任意の全パラメーターとの積でも pushout。 -/
lemma parameterizedSquare_isPushout (T : SSet.{u}) :
    IsPushout (stdSimplex.δ (1 : Fin 3) ▷ T) (stdSimplex.δ (1 : Fin 3) ▷ T)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ▷ T) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ▷ T) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.map (tensorRight T)

/-- 同じ対角で一致する全パラメーターの二三角形を、元の正方形へ貼り合わせる。 -/
def parameterizedSquareLift {T X : SSet.{u}} (a b : (Δ[2] : SSet.{u}) ⊗ T ⟶ X)
    (h : (stdSimplex.δ (1 : Fin 3) ▷ T) ≫ a =
      (stdSimplex.δ (1 : Fin 3) ▷ T) ≫ b) :
    ((Δ[1] : SSet.{u}) ⊗ Δ[1]) ⊗ T ⟶ X :=
  (parameterizedSquare_isPushout T).desc a b h

/-- 同じ貼り合わせの第一三角形は、元の第一三角形を全パラメーターで回収する。 -/
lemma parameterizedSquareLift_zero {T X : SSet.{u}} (a b : (Δ[2] : SSet.{u}) ⊗ T ⟶ X)
    (h : (stdSimplex.δ (1 : Fin 3) ▷ T) ≫ a =
      (stdSimplex.δ (1 : Fin 3) ▷ T) ≫ b) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ▷ T) ≫ parameterizedSquareLift a b h = a :=
  (parameterizedSquare_isPushout T).inl_desc a b h

/-- 同じ貼り合わせの第二三角形は、元の第二三角形を全パラメーターで回収する。 -/
lemma parameterizedSquareLift_one {T X : SSet.{u}} (a b : (Δ[2] : SSet.{u}) ⊗ T ⟶ X)
    (h : (stdSimplex.δ (1 : Fin 3) ▷ T) ≫ a =
      (stdSimplex.δ (1 : Fin 3) ▷ T) ≫ b) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ▷ T) ≫ parameterizedSquareLift a b h = b :=
  (parameterizedSquare_isPushout T).inr_desc a b h

/-- 全パラメーターの正方形の族は、同じ二つの三角形で一意に決まる。 -/
lemma parameterizedSquare_hom_ext {T X : SSet.{u}}
    (H K : ((Δ[1] : SSet.{u}) ⊗ Δ[1]) ⊗ T ⟶ X)
    (h₀ : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ▷ T) ≫ H = (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ▷ T) ≫ K)
    (h₁ : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ▷ T) ≫ H = (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ▷ T) ≫ K) : H = K :=
  (parameterizedSquare_isPushout T).hom_ext h₀ h₁

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
