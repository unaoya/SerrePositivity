module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeHomPathVertices
public import SerrePositivity.InfinityCategories.F1.IntervalHomPathSpan

/-!
概要：同じ底変換比較 path の Hom の二射影は、元の二つの分類 Hom の同値。
方針：構成済みの同じ path の Hom を両端で評価し、元の分類図式へ端点を揃える。
規約：元の二図式全体と元の比較の辺を固定する。
使われ方：底の制限側と底変換後の側の同じ Hom 作用の比較四角形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {C D : Type u} [Category.{u} C] [Category.{u} D] (k : D ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))

/-- 同じ比較 path の Hom の零射影は、元の分類図式を底で制限した Hom への実際の評価。 -/
def cocartesianBaseChangeHomSpanZero :
    cocartesianBaseChangeHomComparisonSpace k p q ⟶ intervalMappingSpace
      (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫
        cocartesianStrictTransportCoherentDiagram p.val.hom))
      (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫
        cocartesianStrictTransportCoherentDiagram q.val.hom)) :=
  intervalHomPathEndpoint (cocartesianBaseChangeHomPath k) 0
    (coherentNerveVertex p) (coherentNerveVertex q)
    (cocartesianBaseChangeHomPath_zero_vertex k p) (cocartesianBaseChangeHomPath_zero_vertex k q)

/-- 同じ比較 path の Hom の一射影は、元の底変換対象の分類 Hom への実際の評価。 -/
def cocartesianBaseChangeHomSpanOne :
    cocartesianBaseChangeHomComparisonSpace k p q ⟶ intervalMappingSpace
      (functorVertex (cocartesianStrictTransportCoherentDiagram
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p).val.hom))
      (functorVertex (cocartesianStrictTransportCoherentDiagram
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q).val.hom)) :=
  intervalHomPathEndpoint (cocartesianBaseChangeHomPath k) 1
    (coherentNerveVertex p) (coherentNerveVertex q)
    (cocartesianBaseChangeHomPath_one_vertex k p) (cocartesianBaseChangeHomPath_one_vertex k q)

/-- 同じ比較 Hom の零射影は、元の Hom の間の全境界を持ち上げる。 -/
lemma cocartesianBaseChangeHomSpanZero_trivialKanFibration :
    TrivialKanFibration (cocartesianBaseChangeHomSpanZero k p q) :=
  intervalHomPathEndpoint_trivialKanFibration _ _ _ _ _ _

/-- 同じ比較 Hom の一射影は、元の Hom の間の全境界を持ち上げる。 -/
lemma cocartesianBaseChangeHomSpanOne_trivialKanFibration :
    TrivialKanFibration (cocartesianBaseChangeHomSpanOne k p q) :=
  intervalHomPathEndpoint_trivialKanFibration _ _ _ _ _ _

end SerrePositivity.InfinityCategories
