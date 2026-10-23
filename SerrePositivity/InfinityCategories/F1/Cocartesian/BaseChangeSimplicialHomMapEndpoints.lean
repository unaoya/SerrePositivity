module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeSimplicialHomSpan
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeHomSpan

/-!
概要：元の比較 Hom の底制限は、元の両端の分類 Hom の同じ制限と厳密に可換。
方針：同じ可逆 path の Hom 後合成の端点自然性を適用する。
規約：元の比較 span と元の図式の制限作用そのもの。
使われ方：既存の cocartesianBaseChangeHomTransport の底制限自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {D C : Type u} [Category.{u} D] [Category.{u} C] {A : SSet.{u + 1}}
  (a : A ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (nerve D)) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C))

/-- 元の零射影と底制限の順序は、同じ比較 Hom の制限に関して厳密に可換。 -/
lemma cocartesianBaseChangeSimplicialHomMap_zero :
    cocartesianBaseChangeHomSpanZero k p q ≫
        intervalDiagramRestriction a
          ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫
            cocartesianStrictTransportCoherentDiagram p.val.hom)
          ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫
            cocartesianStrictTransportCoherentDiagram q.val.hom) =
      cocartesianBaseChangeSimplicialHomMap a k p q ≫
        cocartesianBaseChangeSimplicialHomSpanZero a k p q := by
  exact intervalHomPathMap_endpoint (cocartesianBaseChangeHomPath k)
    ((pre a).app CatInfinity.{u})
    (cocartesianBaseChangeSimplicialHomPath a k) rfl
    (coherentNerveVertex p) (coherentNerveVertex q) 0
    (cocartesianBaseChangeHomPath_zero_vertex k p) (cocartesianBaseChangeHomPath_zero_vertex k q)
    (cocartesianBaseChangeSimplicialHomPath_zero_vertex a k p)
    (cocartesianBaseChangeSimplicialHomPath_zero_vertex a k q)
    (functorVertex_precomposition _ _) (functorVertex_precomposition _ _)

/-- 元の一射影と底制限の順序は、同じ比較 Hom の制限に関して厳密に可換。 -/
lemma cocartesianBaseChangeSimplicialHomMap_one :
    cocartesianBaseChangeHomSpanOne k p q ≫
        intervalDiagramRestriction a
          (cocartesianStrictTransportCoherentDiagram
            ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p).val.hom)
          (cocartesianStrictTransportCoherentDiagram
            ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q).val.hom) =
      cocartesianBaseChangeSimplicialHomMap a k p q ≫
        cocartesianBaseChangeSimplicialHomSpanOne a k p q := by
  exact intervalHomPathMap_endpoint (cocartesianBaseChangeHomPath k)
    ((pre a).app CatInfinity.{u})
    (cocartesianBaseChangeSimplicialHomPath a k) rfl
    (coherentNerveVertex p) (coherentNerveVertex q) 1
    (cocartesianBaseChangeHomPath_one_vertex k p) (cocartesianBaseChangeHomPath_one_vertex k q)
    (cocartesianBaseChangeSimplicialHomPath_one_vertex a k p)
    (cocartesianBaseChangeSimplicialHomPath_one_vertex a k q)
    (functorVertex_precomposition _ _) (functorVertex_precomposition _ _)

end SerrePositivity.InfinityCategories
