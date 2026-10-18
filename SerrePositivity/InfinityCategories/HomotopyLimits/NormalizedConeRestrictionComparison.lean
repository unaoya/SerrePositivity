module

public import SerrePositivity.InfinityCategories.HomotopyLimits.ConeSectionRestrictionCriterion

/-!
概要：錐の固定条件で正規化した slice・切断の制限は共通の両端固定模型への比較と厳密に可換。
方針：一般の図式の等式による移送を恒等射へ戻して既存の二つの制限の自然性を使う。
規約：同値性だけでなく実際の射の等式を保持する。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6、標準の制限の導来 fiber の共通模型。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 概要：図式の等式で終域を正規化した両端固定の錐の制限。
方針：通常の図式の制限に固定条件の等式による移送を後合成する。
規約：頂点 x を全次数で保持する。
使われ方：Kerodon 7.4.1.6、native な slice・切断制限の共通の比較先。 -/
def normalizedEndpointConeRestriction {K J X : SSet.{u}}
    (p : J ⟶ X) (q : K ⟶ X) (f : K ⟶ J) (h : f ≫ p = q) (x : X _⦋0⦌) :
    fixedEndpointConeSpace p x ⟶ fixedEndpointConeSpace q x :=
  endpointConeRestrict p x f ≫
    eqToHom (congrArg (fun r : K ⟶ X ↦ fixedEndpointConeSpace r x) h)

/-- 概要：正規化した slice 制限は共通模型への標準比較と厳密に可換。
方針：終域の図式を等式で置換し、通常の slice の制限の自然性を使う。
規約：図式の固定条件の証明への依存はない。
使われ方：Kerodon 7.4.1.6、slice 制限の導来 fiber を共通模型へ移す。 -/
lemma normalizedSliceEndpointComparison_restrict {K J X : SSet.{u}}
    (p : J ⟶ X) (q : K ⟶ X) (f : K ⟶ J) (h : f ≫ p = q) (x : X _⦋0⦌) :
    vertexFiberMap (sliceOverProjection p) (sliceOverProjection q)
        (sliceOverRestrict p f ≫ eqToHom (congrArg (fun r : K ⟶ X ↦ sliceOver r) h))
        (by rw [Category.assoc, sliceOver_eqToHom_projection h, sliceOverRestrict_projection]) x ≫
      sliceEndpointConeComparison q x =
        sliceEndpointConeComparison p x ≫ normalizedEndpointConeRestriction p q f h x := by
  subst q
  simpa only [normalizedEndpointConeRestriction, eqToHom_refl, Category.comp_id,
    sliceRestrictionFiberMap] using sliceEndpointConeComparison_restrict p x f

/-- 概要：正規化した切断制限は共通模型への標準比較と厳密に可換。
方針：図式の等式を除いて通常の切断制限の自然性に帰着する。
規約：選んだ比較同値の逆の自然性は使わない。
使われ方：Kerodon 7.4.1.6、標準の切断制限の導来 fiber の移送。 -/
lemma normalizedSectionEndpointComparison_restrict {K J X : SSet.{u}}
    (p : J ⟶ X) (q : K ⟶ X) (f : K ⟶ J) (h : f ≫ p = q) (x : X _⦋0⦌) :
    (relativeFunctorPre (sliceUnderProjection (SSet.yonedaEquiv.symm x)) p f ≫
        eqToHom (congrArg (fun r : K ⟶ X ↦ coherentConeSectionSpace r x) h)) ≫
      sectionEndpointConeComparison q x =
        sectionEndpointConeComparison p x ≫ normalizedEndpointConeRestriction p q f h x := by
  subst q
  simpa only [normalizedEndpointConeRestriction, eqToHom_refl, Category.comp_id] using
    sectionEndpointConeComparison_restrict p x f

/-- 概要：coherent な錐の図式から元の図式への両端固定の錐の制限。
方針：右図式への包含と錐の固定条件で正規化した制限を取る。
規約：元の p と頂点 x を厳密に終域に持つ。
使われ方：HTT 4.2.4.1、native な slice と切断の導来 fiber の共通模型。 -/
def coneEndpointRestriction {K X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCone p) (x : X _⦋0⦌) :
    fixedEndpointConeSpace c.val x ⟶ fixedEndpointConeSpace p x :=
  normalizedEndpointConeRestriction c.val p (joinInr (Δ[0] : SSet.{u}) K) c.property x

/-- 概要：native な slice 制限は共通模型への標準比較と厳密に可換。
方針：slice 制限の正規化の式と一般の固定条件付きの自然性を使う。
規約：充填性や極限性は不要。
使われ方：HTT 4.2.4.1、slice 制限の実際の導来 fiber の比較。 -/
lemma coneSliceEndpointComparison_restrict {K X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCone p) (x : X _⦋0⦌) :
    coneSliceRestrictionFiberMap c x ≫ sliceEndpointConeComparison p x =
      sliceEndpointConeComparison c.val x ≫ coneEndpointRestriction c x := by
  have h := normalizedSliceEndpointComparison_restrict c.val p
    (joinInr (Δ[0] : SSet.{u}) K) c.property x
  simpa only [coneSliceRestrictionFiberMap, ← coneSliceOverRestriction_eq,
    coneEndpointRestriction] using h

/-- 概要：native な切断制限は共通模型への標準比較と厳密に可換。
方針：切断制限の定義を正規化した一般の自然性に適用する。
規約：同値性の判定より強い実際の射の等式。
使われ方：HTT 4.2.4.1、標準の切断制限の fiber の実際の比較。 -/
lemma coneSectionEndpointComparison_restrict {K X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCone p) (x : X _⦋0⦌) :
    coneSectionRestriction c x ≫ sectionEndpointConeComparison p x =
      sectionEndpointConeComparison c.val x ≫ coneEndpointRestriction c x :=
  normalizedSectionEndpointComparison_restrict c.val p
    (joinInr (Δ[0] : SSet.{u}) K) c.property x

end
end SerrePositivity.InfinityCategories.HomotopyLimits
