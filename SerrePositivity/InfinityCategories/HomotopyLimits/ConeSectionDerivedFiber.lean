module

public import SerrePositivity.InfinityCategories.HomotopyLimits.RightFibrationHomDerivedFiber
public import SerrePositivity.InfinityCategories.HomotopyLimits.ComparisonFiberPost
public import SerrePositivity.InfinityCategories.HomotopyLimits.ConeSectionLimitCriterion

/-!
概要：任意の coherent な錐の間の pinched Hom と選んだ切断比較の導来 fiber の同値。
方針：right fibration の比較の fiber を、錐の頂点 fiber と切断空間の同値で後合成する。
規約：底の頂点は錐 d の点を選んだ同値で写した点。標準の制限の点との一致は含めない。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6・7.5.4.6、元の q_x へ向かう比較 span。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 概要：任意の錐 d はその頂点からの coslice の切断空間の点を与える。
方針：slice の頂点 fiber の錐の点を、選んだ切断模型との同値で写す。
規約：同値の逆の選択に依存し、標準の制限の点との厳密な一致は主張しない。
使われ方：選んだ切断比較の導来 fiber で固定する底の頂点。 -/
def coneSectionDerivedFiberPoint {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (d : JoinCone p) : (coherentConeSectionSpace p d.vertex) _⦋0⦌ :=
  (coneVertexFiberSectionEquivalence p d.vertex).hom.app _ (coneVertexFiberPoint d)

/-- 概要：錐の頂点 fiber への比較の導来 fiber から切断比較の導来 fiber への実際の射。
方針：頂点 fiber と切断空間の同値による既存の後合成の fiber 射を使う。
規約：固定点は d の頂点 fiber の点から選んだ同値による像へ移す。
使われ方：Kerodon 7.4.1.6・7.5.4.6、pinched Hom の比較を切断模型へ移す。 -/
def coneSectionDerivedFiberMap {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (d c : JoinCone p) :
    comparisonFiber (rightFibrationHomComparison (sliceOverProjection p) c d.vertex)
        (coneVertexFiberPoint d) ⟶
      comparisonFiber (coneSectionHomComparison c d.vertex) (coneSectionDerivedFiberPoint d) :=
  comparisonFiberPost (rightFibrationHomComparison (sliceOverProjection p) c d.vertex)
    (coneVertexFiberSectionEquivalence p d.vertex).hom (coneVertexFiberPoint d)

/-- 概要：切断模型へ移す実際の fiber 射は底の pinched Hom への源成分を保つ。
方針：後合成による fiber 射の源成分の計算を適用する。
規約：底の頂点 x と錐 c の頂点の間の pinched Hom を固定する。
使われ方：選んだ比較と元の写像空間のデータの整合性。 -/
lemma coneSectionDerivedFiberMap_source {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (d c : JoinCone p) :
    coneSectionDerivedFiberMap d c ≫ comparisonFiberSource (coneSectionHomComparison c d.vertex)
        (coneSectionDerivedFiberPoint d) =
      comparisonFiberSource (rightFibrationHomComparison (sliceOverProjection p) c d.vertex)
        (coneVertexFiberPoint d) :=
  comparisonFiberPost_source _ _ _

/-- 概要：切断模型へ移す実際の fiber 射は path を選んだ同値で後合成する。
方針：後合成による fiber 射の path 成分の計算を適用する。
規約：終点は d から得た切断の点へ移る。
使われ方：導来 fiber の底の錐のデータの追跡。 -/
lemma coneSectionDerivedFiberMap_path {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (d c : JoinCone p) :
    coneSectionDerivedFiberMap d c ≫ comparisonFiberPath (coneSectionHomComparison c d.vertex)
        (coneSectionDerivedFiberPoint d) =
      comparisonFiberPath (rightFibrationHomComparison (sliceOverProjection p) c d.vertex)
        (coneVertexFiberPoint d) ≫
          equivalencePathMap (coneVertexFiberSectionEquivalence p d.vertex).hom :=
  comparisonFiberPost_path _ _ _

/-- 概要：錐の頂点 fiber から切断模型へ移す実際の導来 fiber の射はホモトピー同値。
方針：標的の同値が導来 fiber に誘導する実際の比較の同値性を使う。
規約：添字 K と錐 d・c は任意。極限性、可縮性、strict な通常の錐の仮定は不要。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6・7.5.4.6、主比較の切断模型側の同値。 -/
lemma coneSectionDerivedFiberMap_homotopyEquivalence {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (d c : JoinCone p) :
    IsSimplicialHomotopyEquivalence (coneSectionDerivedFiberMap d c) :=
  comparisonFiberPost_homotopyEquivalence _ _
    (coneVertexFiberSectionEquivalence p d.vertex).isQCatEquivalence.isSimplicialHomotopyEquivalence
    (coneVertexFiberPoint d)

/-- 概要：任意の coherent な錐の間の pinched Hom は選んだ切断比較の導来 fiber と同値。
方針：right fibration の選んだ比較の fiber との同値に、標的の同値の実際の fiber 射を合成する。
規約：指定点は選んだ同値による d の像であり、標準の切断制限との照合は後続工程。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6・7.5.4.6、元の q_x との直接比較へ接続する。 -/
def conePinchedHom_sectionComparisonDerivedFiberEquivalence {K X : SSet.{u}}
    [Quasicategory X] {p : K ⟶ X} (d c : JoinCone p) :
    QCatEquivalence (pinchedHom (X := sliceOver p) d c)
      (comparisonFiber (coneSectionHomComparison c d.vertex) (coneSectionDerivedFiberPoint d)) :=
  (rightFibrationPinchedHomComparisonDerivedFiberEquivalence (sliceOverProjection p) c d.vertex
    (coneVertexFiberPoint d)).trans
      (coneSectionDerivedFiberMap_homotopyEquivalence d c).isQCatEquivalence.choose

end
end SerrePositivity.InfinityCategories.HomotopyLimits
