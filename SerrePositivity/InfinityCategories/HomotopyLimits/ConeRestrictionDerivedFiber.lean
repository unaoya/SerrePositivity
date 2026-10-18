module

public import SerrePositivity.InfinityCategories.HomotopyLimits.ConeSliceDerivedFiber
public import SerrePositivity.InfinityCategories.HomotopyLimits.ConeEndpointPoints
public import SerrePositivity.InfinityCategories.HomotopyLimits.NormalizedConeRestrictionComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.ComparisonFiberPost

/-!
概要：任意の coherent な錐の pinched Hom と標準の切断制限の導来 fiber の同値。
方針：slice・切断の制限を同じ両端固定模型の導来 fiber に移し、標準の錐の点を照合する。
規約：固定点は標準の coherentConeSectionPoint d。選んだ切断比較の像に変更しない。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6・7.5.4.6、元の q_x へ接続する native な fiber 比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 概要：native な slice 制限の導来 fiber から両端固定模型の制限の導来 fiber への実際の射。
方針：標的の標準比較で後合成し、源の標準比較による同じ底上の fiber 射を合成する。
規約：底の点 b は標的の標準比較で写す。
使われ方：Kerodon 7.4.1.6、slice 制限と標準の切断制限の共通模型への移送。 -/
def coneSliceEndpointDerivedFiberMap {K X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCone p) (x : X _⦋0⦌) (b : (vertexFiber (sliceOverProjection p) x) _⦋0⦌) :
    comparisonFiber (coneSliceRestrictionFiberMap c x) b ⟶
      comparisonFiber (coneEndpointRestriction c x) ((sliceEndpointConeComparison p x).app _ b) :=
  comparisonFiberPost (coneSliceRestrictionFiberMap c x) (sliceEndpointConeComparison p x) b ≫
    comparisonFiberMap (coneSliceRestrictionFiberMap c x ≫ sliceEndpointConeComparison p x)
      (coneEndpointRestriction c x) (sliceEndpointConeComparison c.val x)
      (coneSliceEndpointComparison_restrict c x).symm ((sliceEndpointConeComparison p x).app _ b)

/-- 概要：slice 制限から共通模型への実際の導来 fiber の射はホモトピー同値。
方針：源・標的の二つの標準比較の同値性をそれぞれ fiber の比較へ適用する。
規約：K と c は任意、X の quasicategory 性のみを要求する。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6、pinched Hom の共通模型への同値。 -/
lemma coneSliceEndpointDerivedFiberMap_homotopyEquivalence {K X : SSet.{u}}
    [Quasicategory X] {p : K ⟶ X} (c : JoinCone p) (x : X _⦋0⦌)
    (b : (vertexFiber (sliceOverProjection p) x) _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (coneSliceEndpointDerivedFiberMap c x b) :=
  (comparisonFiberPost_homotopyEquivalence _ _
    (sliceEndpointConeComparison_homotopyEquivalence p x) b).comp
      (comparisonFiberMap_homotopyEquivalence _ _ _ _
        (sliceEndpointConeComparison_homotopyEquivalence c.val x) _)

/-- 概要：標準の切断制限の導来 fiber から両端固定模型の制限の導来 fiber への実際の射。
方針：標的の標準比較による後合成と源の標準比較による fiber 射を合成する。
規約：選んだ同値の逆の自然性は用いず、標準比較の厳密な可換式を使う。
使われ方：Kerodon 7.4.1.6、元の q_x の fiber と pinched Hom の間の共通模型。 -/
def coneSectionEndpointDerivedFiberMap {K X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCone p) (x : X _⦋0⦌) (b : (coherentConeSectionSpace p x) _⦋0⦌) :
    comparisonFiber (coneSectionRestriction c x) b ⟶
      comparisonFiber (coneEndpointRestriction c x)
        ((sectionEndpointConeComparison p x).app _ b) :=
  comparisonFiberPost (coneSectionRestriction c x) (sectionEndpointConeComparison p x) b ≫
    comparisonFiberMap (coneSectionRestriction c x ≫ sectionEndpointConeComparison p x)
      (coneEndpointRestriction c x) (sectionEndpointConeComparison c.val x)
      (coneSectionEndpointComparison_restrict c x).symm
      ((sectionEndpointConeComparison p x).app _ b)

/-- 概要：標準の切断制限から共通模型への実際の導来 fiber の射はホモトピー同値。
方針：源・標的の標準比較の同値性と二つの fiber 比較を合わせる。
規約：極限性、比較射の同値性、fiber の可縮性・非空性は仮定しない。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6・7.5.4.6、標準の切断制限の fiber の同定。 -/
lemma coneSectionEndpointDerivedFiberMap_homotopyEquivalence {K X : SSet.{u}}
    [Quasicategory X] {p : K ⟶ X} (c : JoinCone p) (x : X _⦋0⦌)
    (b : (coherentConeSectionSpace p x) _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (coneSectionEndpointDerivedFiberMap c x b) :=
  (comparisonFiberPost_homotopyEquivalence _ _
    (sectionEndpointConeComparison_homotopyEquivalence p x) b).comp
      (comparisonFiberMap_homotopyEquivalence _ _ _ _
        (sectionEndpointConeComparison_homotopyEquivalence c.val x) _)

/-- 概要：任意の coherent な錐の間の pinched Hom は標準の切断制限の導来 fiber と同値。
方針：slice 制限の fiber との同値を共通模型へ移し、標準の錐の点の一致で切断側へ戻す。
規約：固定点は元の d に付随する標準の切断の点。極限性や可縮性は不要。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6・7.5.4.6、元の q_x の fiber への直接比較の出口。 -/
def conePinchedHom_sectionRestrictionDerivedFiberEquivalence {K X : SSet.{u}}
    [Quasicategory X] {p : K ⟶ X} (d c : JoinCone p) :
    QCatEquivalence (pinchedHom (X := sliceOver p) d c)
      (comparisonFiber (coneSectionRestriction c d.vertex) (coherentConeSectionPoint d)) := by
  let e₁ := conePinchedHom_sliceRestrictionDerivedFiberEquivalence d c
  let e₂ := (coneSliceEndpointDerivedFiberMap_homotopyEquivalence c d.vertex
    (coneVertexFiberPoint d)).isQCatEquivalence.choose
  let e₃ := (coneSectionEndpointDerivedFiberMap_homotopyEquivalence c d.vertex
    (coherentConeSectionPoint d)).isQCatEquivalence.choose
  have e : QCatEquivalence (pinchedHom (X := sliceOver p) d c)
      (comparisonFiber (coneEndpointRestriction c d.vertex)
        ((sectionEndpointConeComparison p d.vertex).app _ (coherentConeSectionPoint d))) := by
    simpa only [coneEndpointComparison_point_eq] using e₁.trans e₂
  exact e.trans e₃.symm

end
end SerrePositivity.InfinityCategories.HomotopyLimits
