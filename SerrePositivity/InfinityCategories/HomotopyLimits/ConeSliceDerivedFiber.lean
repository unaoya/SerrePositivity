module

public import SerrePositivity.InfinityCategories.HomotopyLimits.ComparisonFiberFunctor
public import SerrePositivity.InfinityCategories.HomotopyLimits.ConeSliceRestrictionCriterion

/-!
概要：任意の coherent な錐の pinched Hom と native な slice 制限の導来 fiber の実際の比較。
方針：比較 span と錐の図式上の slice の厳密な同型を同じ底上の fiber の射へ移す。
規約：切断の選択を介さず、固定点は元の錐 d の頂点 fiber の点を保持する。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6・7.5.4.6、標準の切断制限へ向かう比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 概要：比較 span の始点評価の導来 fiber から native な slice 制限の導来 fiber への射。
方針：錐の図式上の slice との厳密な同型を、同じ底上の源の比較として使う。
規約：底の点 b と可逆 path は変更しない。
使われ方：Kerodon 7.4.1.6、pinched Hom の実際の fiber 表示を制限射へ移す。 -/
def coneSliceDerivedFiberMap {K X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCone p) (x : X _⦋0⦌) (b : (vertexFiber (sliceOverProjection p) x) _⦋0⦌) :
    comparisonFiber (rightFibrationMappingEvaluation (sliceOverProjection p) c x) b ⟶
      comparisonFiber (coneSliceRestrictionFiberMap c x) b :=
  comparisonFiberMap (rightFibrationMappingEvaluation (sliceOverProjection p) c x)
    (coneSliceRestrictionFiberMap c x) (coneMappingTotalIso c x).hom
    (coneMappingTotalIso_evaluation c x) b

/-- 概要：slice 制限への実際の fiber 射は中間模型の同型と源成分で厳密に可換。
方針：同じ底上の fiber 射の源成分の式を適用する。
規約：底は slice 射影の x 上の頂点 fiber そのもの。
使われ方：導来 fiber の比較と元の slice 制限のデータの整合性。 -/
lemma coneSliceDerivedFiberMap_source {K X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCone p) (x : X _⦋0⦌) (b : (vertexFiber (sliceOverProjection p) x) _⦋0⦌) :
    coneSliceDerivedFiberMap c x b ≫ comparisonFiberSource (coneSliceRestrictionFiberMap c x) b =
      comparisonFiberSource (rightFibrationMappingEvaluation (sliceOverProjection p) c x) b ≫
        (coneMappingTotalIso c x).hom :=
  comparisonFiberMap_source _ _ _ _ _

/-- 概要：比較 span から native な slice 制限への実際の導来 fiber の射はホモトピー同値。
方針：源の厳密な同型による同じ底上の fiber の比較を使う。
規約：X の quasicategory 性以外に、極限性や fiber の可縮性の前提を置かない。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6・7.5.4.6、選んだ切断を介さない比較。 -/
lemma coneSliceDerivedFiberMap_homotopyEquivalence {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (c : JoinCone p) (x : X _⦋0⦌)
    (b : (vertexFiber (sliceOverProjection p) x) _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (coneSliceDerivedFiberMap c x b) :=
  comparisonFiberMap_homotopyEquivalence _ _ _ _
    (homotopyEquivalence_of_isIso (coneMappingTotalIso c x).hom) b

/-- 概要：任意の coherent な錐の間の pinched Hom は native な slice 制限の導来 fiber と同値。
方針：始点評価の fiber との同値と、中間空間の同型から誘導した実際の fiber 射を合成する。
規約：固定点は元の錐 d の点であり、選んだ切断比較への変更は行わない。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6・7.5.4.6、標準の切断制限の fiber との比較。 -/
def conePinchedHom_sliceRestrictionDerivedFiberEquivalence {K X : SSet.{u}}
    [Quasicategory X] {p : K ⟶ X} (d c : JoinCone p) :
    QCatEquivalence (pinchedHom (X := sliceOver p) d c)
      (comparisonFiber (coneSliceRestrictionFiberMap c d.vertex) (coneVertexFiberPoint d)) :=
  (conePinchedHom_mappingEvaluationDerivedFiberEquivalence d c).trans
    (coneSliceDerivedFiberMap_homotopyEquivalence c d.vertex
      (coneVertexFiberPoint d)).isQCatEquivalence.choose

end
end SerrePositivity.InfinityCategories.HomotopyLimits
