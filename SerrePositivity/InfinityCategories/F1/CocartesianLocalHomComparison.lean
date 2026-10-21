module

public import SerrePositivity.InfinityCategories.F1.CocartesianOneCellHomComparison
public import SerrePositivity.InfinityCategories.F1.CocartesianZeroSimplexEquivalence

/-!
概要：元の底の任意の通常圏のセル上の Hom を、元の分類図式の同じ制限と比較する。
方針：元の局所分類作用と既存の元の比較 path の輸送を合成する。
規約：零・一次元では追加仮定なしの既存の同じ比較となる。
使われ方：元の分類 Hom 作用の Segal 比較の局所入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 元の底のセル上の全相対 Hom を、元の分類図式を同じセルへ制限した Hom へ写す。 -/
def cocartesianLocalHomComparison
    {C D : Type u} [Category.{u} C] [Category.{u} D] (k : D ⥤ C)
    (p q : CocartesianFibrationCategory (nerve C)) :
    (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)) ⟶
      intervalMappingSpace
        (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫
          cocartesianStrictTransportCoherentDiagram p.val.hom))
        (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫
          cocartesianStrictTransportCoherentDiagram q.val.hom)) :=
  cocartesianStraighteningHomInterval
    ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
    ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q) ≫
      cocartesianBaseChangeHomTransport k p q

/-- 一次元セルでは既存の元の同じ局所比較そのもの。 -/
lemma cocartesianLocalHomComparison_oneCell
    {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin 2) ⥤ C)
    (p q : CocartesianFibrationCategory (nerve C)) :
    cocartesianLocalHomComparison k p q = cocartesianOneCellHomComparison k p q := rfl

/-- 元の零次元セル上の同じ局所 Hom 比較は同値。 -/
lemma cocartesianLocalHomComparison_zeroCell_isQCatEquivalence
    {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin 1) ⥤ C)
    (p q : CocartesianFibrationCategory (nerve C)) :
    IsQCatEquivalence (cocartesianLocalHomComparison k p q) :=
  (cocartesianStraighteningHomInterval_zeroSimplex_isQCatEquivalence _ _).comp
    (cocartesianBaseChangeHomTransport_isQCatEquivalence k p q)

/-- 元の一次元セル上の同じ局所 Hom 比較は同値。 -/
lemma cocartesianLocalHomComparison_oneCell_isQCatEquivalence
    {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin 2) ⥤ C)
    (p q : CocartesianFibrationCategory (nerve C)) :
    IsQCatEquivalence (cocartesianLocalHomComparison k p q) :=
  cocartesianOneCellHomComparison_isQCatEquivalence k p q

end SerrePositivity.InfinityCategories
