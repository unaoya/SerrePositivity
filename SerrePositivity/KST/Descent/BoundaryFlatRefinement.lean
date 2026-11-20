module

public import SerrePositivity.KST.Descent.BoundaryBlowupDensity
public import SerrePositivity.KST.Descent.ComponentFlatRefinement

/-!
# 境界基本開からの strict transform の全射性と有限平坦細分

## 概要
平坦化に使った D(r) の逆像の稠密性により、同じ開部分から構成した strict transform の全射性を得る。

## 方針
境界の非零因子性を blowup の稠密性へ移し、有限射の閉像性を使う。

## 規約
D(r) を中心の補集合と同一視しない。

## 使われ方
論文 補題 3.3、公理 (6) の実際のアフィン平坦化を有限忠実平坦な細分に接続する。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open SerrePositivity.KST.SchemeLemmas

namespace SerrePositivity.KST.Descent

/-- 概要：非零因子の境界からの有限全射の strict transform は全射（論文 補題 3.3）。
方針：blowup 上の境界基本開の稠密性と有限な strict transform の全射性判定を使う。
規約：中心の補集合と D(r) の一致や、元の射の開部分上の同型性は不要。
使われ方：加群平坦化と同じ境界での実際の有限忠実平坦被覆。 -/
theorem strictTransformπ_boundary_surjective {X Y : Scheme.{u}} [IsAffine Y]
    (f : X ⟶ Y) [IsFinite f] [Surjective f] (J : Y.IdealSheafData)
    (r : Γ(Y, ⊤)) (hr : r ∈ nonZeroDivisors Γ(Y, ⊤)) :
    Surjective (_root_.SerrePositivity.AlgebraicGeometry.strictTransformπ f (Y.basicOpen r) J) :=
  strictTransformπ_surjective_of_dense f (Y.basicOpen r) J
    (blowup_boundary_dense_of_isAffine J r hr)

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FiniteTypeSchemes S}
  (f : X ⟶ Y) [IsFinite f.hom.left] [IsAffine Y.obj.left]

/-- 概要：整成分の同じ境界基本開での平坦化から元の射を細分する有限忠実平坦被覆を得る（補題 3.3）。
方針：実際の strict transform を使い、境界の稠密性から全射性、元の二射影から細分射を構成する。
規約：D(r) と中心補集合の一致は要求しない。平坦性はその同じ D(r) で定義した構造射の入力。
使われ方：生成点付近の自由化・チャート平坦化から元の有限全射の Čech 計算への接続。 -/
theorem exists_finiteFlat_cover_refining_boundary
    (c : IrreducibleComponentIndex X) (hc : Surjective (integralComponentMap f c).hom.left)
    (J : Y.obj.left.IdealSheafData) (r : Γ(Y.obj.left, ⊤))
    (hr : r ∈ nonZeroDivisors Γ(Y.obj.left, ⊤))
    [Flat (_root_.SerrePositivity.AlgebraicGeometry.strictTransformπ (integralComponentMap f c).hom.left (Y.obj.left.basicOpen r) J)] :
    ∃ (T : FiniteTypeSchemes S) (p : T ⟶ finiteTypeBlowup Y J)
      (a : T ⟶ finiteTypePullback f (finiteTypeBlowupProjection Y J)),
      IsFinite p.hom.left ∧ Flat p.hom.left ∧ Surjective p.hom.left ∧
        LocallyOfFinitePresentation p.hom.left ∧
        a ≫ finiteTypePullbackSnd f (finiteTypeBlowupProjection Y J) = p := by
  have : IsFinite (integralComponentMap f c).hom.left := integralComponentMap_isFinite f c
  have : Surjective (integralComponentMap f c).hom.left := hc
  let U := Y.obj.left.basicOpen r
  let T := finiteTypeStrictTransform (integralComponentMap f c) U J
  let p : T ⟶ finiteTypeBlowup Y J :=
    finiteTypeStrictTransformProjection (integralComponentMap f c) U J
  let q : T ⟶ X := finiteTypeStrictTransformToOriginal (integralComponentMap f c) U J ≫
    integralComponentInclusion X c
  have hq : q ≫ f = p ≫ finiteTypeBlowupProjection Y J :=
    (Category.assoc _ _ _).trans (finiteTypeStrictTransform_comm (integralComponentMap f c) U J)
  let a : T ⟶ finiteTypePullback f (finiteTypeBlowupProjection Y J) :=
    (finiteTypePullback_isPullback f (finiteTypeBlowupProjection Y J)).lift q p hq
  exact ⟨T, p, a, strictTransformπ_isFinite (integralComponentMap f c).hom.left U J,
    (inferInstance : Flat
      (_root_.SerrePositivity.AlgebraicGeometry.strictTransformπ (integralComponentMap f c).hom.left (Y.obj.left.basicOpen r) J)),
    strictTransformπ_boundary_surjective (integralComponentMap f c).hom.left J r hr,
    strictTransformπ_locallyOfFinitePresentation (integralComponentMap f c).hom.left U J,
    (finiteTypePullback_isPullback f (finiteTypeBlowupProjection Y J)).lift_snd _ _ _⟩

end SerrePositivity.KST.Descent
