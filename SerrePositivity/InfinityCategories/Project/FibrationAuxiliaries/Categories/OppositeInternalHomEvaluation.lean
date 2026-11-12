module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrismOpposite

/-!
概要：内部 Hom の反転同型は実際の評価と curry を保つ。
方針：指数比較の評価公式と反転の直積比較を用いる。
規約：単体集合と射は任意で、Kan 性は不要。
使われ方：反転した一点 Hom の合成作用の同型性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

local instance : SSet.opFunctor.{u}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor

/-- 概要：反転の逆直積比較は直積と反転の標準同型。
方針：直積比較が各成分をそのまま返すことを使う。
規約：二つの単体集合は同じ宇宙。
使われ方：指数比較の評価公式の正規化。 -/
lemma opposite_prodComparison_inv (K A : SSet.{u}) :
    inv (prodComparison SSet.opFunctor K A) = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.opTensorIso K A).hom := by
  have h : prodComparison SSet.opFunctor K A = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.opTensorIso K A).inv := rfl
  apply IsIso.inv_eq_of_hom_inv_id
  rw [h, Iso.inv_hom_id]

/-- 概要：内部 Hom の反転比較の展開は評価射の反転。
方針：標準指数比較の評価公式に反転の直積の式を代入する。
規約：同型は HomotopyLimits の既存の反転同型。
使われ方：任意の反転したパラメーター付き作用の評価。 -/
lemma oppositeInternalHomIso_uncurry (K B : SSet.{u}) :
    uncurry (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso K B).hom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.opTensorIso K ((ihom K).obj B)).hom ≫ SSet.opFunctor.map ((ihom.ev K).app B) := by
  change uncurry ((expComparison SSet.opFunctor K).natTrans.app B) = _
  rw [uncurry_expComparison, opposite_prodComparison_inv]

/-- 概要：内部 Hom の反転同型を通した任意の族の展開は元の展開の反転。
方針：curry の自然性と反転比較の評価公式を使う。
規約：パラメーター A も反転する。
使われ方：反転した豊穣合成の curry を同型の合成として表示する。 -/
lemma oppositeInternalHom_map_uncurry {K B A : SSet.{u}} (f : A ⟶ (ihom K).obj B) :
    uncurry (SSet.opFunctor.map f ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso K B).hom) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.opTensorIso K A).hom ≫ SSet.opFunctor.map (uncurry f) := by
  rw [uncurry_natural_left, oppositeInternalHomIso_uncurry]
  have h : (K.op ◁ SSet.opFunctor.map f) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.opTensorIso K ((ihom K).obj B)).hom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.opTensorIso K A).hom ≫ SSet.opFunctor.map (K ◁ f) := rfl
  rw [← Category.assoc, h, Category.assoc, ← SSet.opFunctor.map_comp, ← uncurry_eq]

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
