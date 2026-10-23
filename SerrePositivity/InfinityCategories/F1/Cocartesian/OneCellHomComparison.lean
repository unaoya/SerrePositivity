module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.OneSimplexEquivalence
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeHomTransport

/-!
概要：一次元セルの元の Hom と、元の分類図式を同じセルへ制限した Hom を同値で比較する。
方針：同じ局所分類作用と元の比較 path の輸送を合成し、元の大域作用との四角形を示す。
規約：局所の同値だけで大域の充満忠実性を結論せず、同じ作用との関手同型を明示する。
使われ方：元の分類 Hom 比較のセルによる降下の一次元の入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

variable {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin 2) ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))

/-- 同じ一次元セル上の元の Hom を、同じ分類図式の制限の Hom へ写す。 -/
def cocartesianOneCellHomComparison :
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

/-- 一次元セル上の同じ Hom 比較は、追加仮定なしに同値。 -/
lemma cocartesianOneCellHomComparison_isQCatEquivalence :
    IsQCatEquivalence (cocartesianOneCellHomComparison k p q) :=
  (cocartesianStraighteningHomInterval_oneSimplex_isQCatEquivalence _ _).comp
    (cocartesianBaseChangeHomTransport_isQCatEquivalence k p q)

/-- 一次元セルの同じ局所 Hom 比較は、元の大域 Hom 作用と関手同型で整合する。 -/
def cocartesianOneCellHomComparisonNaturalityIso :
    FunctorIso ((SSet.uliftFunctor.{u + 1, u}).map
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).map p q) ≫
        cocartesianOneCellHomComparison k p q)
      (cocartesianStraighteningHomInterval p q ≫
        intervalDiagramRestriction ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k))
          (cocartesianStrictTransportCoherentDiagram p.val.hom)
          (cocartesianStrictTransportCoherentDiagram q.val.hom)) :=
  cocartesianBaseChangeHomNaturalityIso k p q

end SerrePositivity.InfinityCategories
