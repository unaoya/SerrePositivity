module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.TwoSimplexEquivalence
public import SerrePositivity.InfinityCategories.F1.Cocartesian.LocalHomComparison

/-!
概要：任意の底の二次元セル上の同じ元の全局所 Hom 比較も同値。
方針：元の二単体 Hom 作用と既存の同じ底変換 Hom 輸送を合成する。
規約：元の全局所 Hom と構成済みの分類図式を保持する。
使われ方：同じ元の分類 Hom 作用の高次単体と骨格への降下。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 元の二次元セル上の同じ局所 Hom 比較は、追加仮定なしに同値。 -/
lemma cocartesianLocalHomComparison_twoCell_isQCatEquivalence
    {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin 3) ⥤ C)
    (p q : CocartesianFibrationCategory (nerve C)) :
    IsQCatEquivalence (cocartesianLocalHomComparison k p q) :=
  (cocartesianStraighteningHomInterval_twoSimplex_isQCatEquivalence _ _).comp
    (cocartesianBaseChangeHomTransport_isQCatEquivalence k p q)

end SerrePositivity.InfinityCategories
