module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.ZeroSimplexEquivalence
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeHomTransport

/-!
概要：零次元セルの元の Hom と、元の分類図式を同じセルへ制限した Hom を同値で比較する。
方針：同じ局所分類作用と元の比較 path の輸送を合成し、元の大域作用との四角形を示す。
規約：局所の同値だけで大域の充満忠実性を結論せず、同じ作用との関手同型を明示する。
使われ方：元の分類 Hom 比較のセルによる降下の零次元の入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

variable {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin 1) ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))

/-- 同じ零次元セル上の元の Hom を、同じ分類図式の制限の Hom へ写す。 -/
def cocartesianZeroCellHomComparison :
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

/-- 零次元セル上の同じ Hom 比較は、追加仮定なしに同値。 -/
lemma cocartesianZeroCellHomComparison_isQCatEquivalence :
    IsQCatEquivalence (cocartesianZeroCellHomComparison k p q) :=
  (cocartesianStraighteningHomInterval_zeroSimplex_isQCatEquivalence _ _).comp
    (cocartesianBaseChangeHomTransport_isQCatEquivalence k p q)

/-- 零次元セルの同じ局所 Hom 比較は、元の大域 Hom 作用と関手同型で整合する。 -/
def cocartesianZeroCellHomComparisonNaturalityIso :
    FunctorIso ((SSet.uliftFunctor.{u + 1, u}).map
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).map p q) ≫
        cocartesianZeroCellHomComparison k p q)
      (cocartesianStraighteningHomInterval p q ≫
        intervalDiagramRestriction ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k))
          (cocartesianStrictTransportCoherentDiagram p.val.hom)
          (cocartesianStrictTransportCoherentDiagram q.val.hom)) :=
  cocartesianBaseChangeHomNaturalityIso k p q

end SerrePositivity.InfinityCategories
