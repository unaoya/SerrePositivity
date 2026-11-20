module

public import SerrePositivity.KST.Descent.DominatingComponent
public import SerrePositivity.KST.Descent.FiniteTypeStrictTransform

/-!
# 支配する整成分の平坦化から元の有限全射の細分

## 概要
支配する成分の実際の strict transform が平坦なら、元の射の底変換を細分する有限忠実平坦被覆を得る。

## 方針
strict transform の二つの射を成分の包含と合成し、元の射の引き戻しの普遍性を使う。

## 規約
平坦化中心の存在は入力ではなく別工程で証明すべき課題。ここでは指定中心での実際の平坦性を要求する。

## 使われ方
論文 補題 3.3 の「支配する整成分 → 平坦化 → 有限忠実平坦な細分」の後半。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open SerrePositivity.KST.SchemeLemmas

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FiniteTypeSchemes S}
  (f : X ⟶ Y) [IsFinite f.hom.left]

/-- 概要：全射な整成分の平坦化から元の有限射の底変換を細分する有限忠実平坦被覆を得る（補題 3.3）。
方針：実際の strict transform を被覆とし、成分の包含と二射影の可換式で元の引き戻しへ写す。
規約：中心 J と実際の strict transform の平坦性を明示する。有限全射降下を仮定しない。
使われ方：元の被覆の Čech 図式へ細分を適用する際の実際の被覆と細分射。 -/
theorem exists_finiteFlat_cover_refining_blowup
    (c : IrreducibleComponentIndex X) (hc : Surjective (integralComponentMap f c).hom.left)
    (J : Y.obj.left.IdealSheafData)
    [Flat (_root_.SerrePositivity.AlgebraicGeometry.strictTransformπ (integralComponentMap f c).hom.left (_root_.SerrePositivity.AlgebraicGeometry.centerComplement J) J)] :
    ∃ (T : FiniteTypeSchemes S) (p : T ⟶ finiteTypeBlowup Y J)
      (a : T ⟶ finiteTypePullback f (finiteTypeBlowupProjection Y J)),
      IsFinite p.hom.left ∧ Flat p.hom.left ∧ Surjective p.hom.left ∧
        LocallyOfFinitePresentation p.hom.left ∧
        a ≫ finiteTypePullbackSnd f (finiteTypeBlowupProjection Y J) = p := by
  have : IsFinite (integralComponentMap f c).hom.left := integralComponentMap_isFinite f c
  have : Surjective (integralComponentMap f c).hom.left := hc
  let T := finiteTypeStrictTransform (integralComponentMap f c) (_root_.SerrePositivity.AlgebraicGeometry.centerComplement J) J
  let p : T ⟶ finiteTypeBlowup Y J :=
    finiteTypeStrictTransformProjection (integralComponentMap f c) (_root_.SerrePositivity.AlgebraicGeometry.centerComplement J) J
  let q : T ⟶ X :=
    finiteTypeStrictTransformToOriginal (integralComponentMap f c) (_root_.SerrePositivity.AlgebraicGeometry.centerComplement J) J ≫
      integralComponentInclusion X c
  have hq : q ≫ f = p ≫ finiteTypeBlowupProjection Y J :=
    (Category.assoc _ _ _).trans
      (finiteTypeStrictTransform_comm (integralComponentMap f c) (_root_.SerrePositivity.AlgebraicGeometry.centerComplement J) J)
  let a : T ⟶ finiteTypePullback f (finiteTypeBlowupProjection Y J) :=
    (finiteTypePullback_isPullback f (finiteTypeBlowupProjection Y J)).lift q p hq
  obtain ⟨hfinite, hflat, hsurj, hfp⟩ :=
    finiteTypeStrictTransform_flatCover (integralComponentMap f c) J
  exact ⟨T, p, a, hfinite, hflat, hsurj, hfp,
    (finiteTypePullback_isPullback f (finiteTypeBlowupProjection Y J)).lift_snd _ _ _⟩

end SerrePositivity.KST.Descent
