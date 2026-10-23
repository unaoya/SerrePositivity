module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeSimplicialHomCorrection
public import SerrePositivity.InfinityCategories.F1.KanSquareFiberEquivalence
public import SerrePositivity.InfinityCategories.F1.IntervalDiagramRestrictionFibration

/-!
概要：任意の単射な境界で指定値を固定した、元の Hom 輸送の補正射は fiber ごとに同値。
方針：元の制限正方形の全空間・底の同値と Kan fibration 性を同じ fiber の射へ移す。
規約：構成した同じ補正輸送と固定境界値を使う。
使われ方：セルの境界固定の分類先 Hom の比較を、同じ底変換の表示へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {D C : Type u} [Category.{u} D] [Category.{u} C] {A : SSet.{u + 1}}
  (a : A ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (nerve D)) [Mono a] (k : D ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))

instance cocartesianBaseChangeSimplicialRestrictionOne_fibration :
    Fibration (cocartesianBaseChangeSimplicialRestrictionOne a k p q) :=
    intervalDiagramRestriction_fibration a
      (cocartesianStrictTransportCoherentDiagram
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p).val.hom)
      (cocartesianStrictTransportCoherentDiagram
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q).val.hom)
instance cocartesianBaseChangeSimplicialRestrictionZero_fibration :
    Fibration (cocartesianBaseChangeSimplicialRestrictionZero a k p q) :=
    intervalDiagramRestriction_fibration a
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫
        cocartesianStrictTransportCoherentDiagram p.val.hom)
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫
        cocartesianStrictTransportCoherentDiagram q.val.hom)

attribute [local instance] vertexFiber_quasicategory_of_innerFibration

/-- 同じ境界値を固定した補正 Hom 輸送の実際の fiber の射は同値。 -/
lemma cocartesianBaseChangeSimplicialBoundaryFiberTransport_isQCatEquivalence
    (r : (intervalMappingSpace
      (functorVertex (a ≫ cocartesianStrictTransportCoherentDiagram
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p).val.hom))
      (functorVertex (a ≫ cocartesianStrictTransportCoherentDiagram
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q).val.hom))) _⦋0⦌) :
    IsQCatEquivalence (cocartesianBaseChangeSimplicialBoundaryFiberTransport a k p q r) := by
  exact kanSquareFiberMap_isQCatEquivalence
    (cocartesianBaseChangeSimplicialRestrictionOne a k p q)
    (cocartesianBaseChangeSimplicialRestrictionZero a k p q)
    (cocartesianBaseChangeSimplicialCorrectedHomTransport a k p q)
    (cocartesianBaseChangeSimplicialHomTransport a k p q)
    (cocartesianBaseChangeSimplicialCorrectedHomTransport_comm a k p q) r
    (cocartesianBaseChangeSimplicialCorrectedHomTransport_isQCatEquivalence a k p q)
    (cocartesianBaseChangeSimplicialHomTransport_isQCatEquivalence a k p q)

end SerrePositivity.InfinityCategories
