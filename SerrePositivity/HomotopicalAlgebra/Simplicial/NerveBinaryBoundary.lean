module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.BinaryCotensor
public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveBiparameterMaps

/-!
# 中断した任意モデル源への一般化：NerveBinaryBoundary

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Gluing two whole moving systems on a pointwise binary coproduct diagram。

## 方針（定義・証明）
bar型の鎖パラメータと整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0458][inventory]を参照する。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0458
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Gluing two whole moving systems on a pointwise binary coproduct diagram
-/

@[expose] public section
universe w uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalClosed
open SerrePositivity.NerveSimplexEndpoint

namespace SerrePositivity.SimplicialModel.NerveBinaryBoundary
variable {D : Type uD} [Category.{vD} D] (B C Q F : D ⥤ SSet.{w})
  (l : B ⟶ Q) (r : C ⟶ Q) (hQ : ∀ d, IsColimit (BinaryCofan.mk (l.app d) (r.app d)))
  (b : NerveBiparameter.System B F) (c : NerveBiparameter.System C F)

/-- Retain both given whole coherent systems in the actual coproduct diagram. -/
def glue : NerveBiparameter.System Q F where
  app s := BinaryCotensor.glue (hQ (NerveSimplexStart.start s)) (b.app s) (c.app s)
  naturality {s t} f := by
    apply BinaryCotensor.hom_ext (hQ (NerveSimplexStart.start t))
    · simp only [Category.assoc, BinaryCotensor.glue_left]
      have hn := (NerveBiparameterMaps.restriction B Q F l).naturality f
      rw [NerveBiparameterMaps.restriction_app, NerveBiparameterMaps.restriction_app] at hn
      have hg := BinaryCotensor.glue_left (hQ (NerveSimplexStart.start s)) (b.app s) (c.app s)
      exact (b.naturality f).trans
        ((congrArg (fun k => k ≫ (NerveBiparameter.values B F).map f) hg.symm).trans
          ((Category.assoc _ _ _).trans (congrArg (fun k => BinaryCotensor.glue
            (hQ (NerveSimplexStart.start s)) (b.app s) (c.app s) ≫ k) hn.symm)))
    · simp only [Category.assoc, BinaryCotensor.glue_right]
      have hn := (NerveBiparameterMaps.restriction C Q F r).naturality f
      rw [NerveBiparameterMaps.restriction_app, NerveBiparameterMaps.restriction_app] at hn
      have hg := BinaryCotensor.glue_right (hQ (NerveSimplexStart.start s)) (b.app s) (c.app s)
      exact (c.naturality f).trans
        ((congrArg (fun k => k ≫ (NerveBiparameter.values C F).map f) hg.symm).trans
          ((Category.assoc _ _ _).trans (congrArg (fun k => BinaryCotensor.glue
            (hQ (NerveSimplexStart.start s)) (b.app s) (c.app s) ≫ k) hn.symm)))

lemma glue_left : glue B C Q F l r hQ b c ≫
    NerveBiparameterMaps.restriction B Q F l = b := by
  apply NatTrans.ext
  funext s
  change (glue B C Q F l r hQ b c).app s ≫ _ = _
  rw [NerveBiparameterMaps.restriction_app]
  exact BinaryCotensor.glue_left (hQ (NerveSimplexStart.start s)) (b.app s) (c.app s)

lemma glue_right : glue B C Q F l r hQ b c ≫
    NerveBiparameterMaps.restriction C Q F r = c := by
  apply NatTrans.ext
  funext s
  change (glue B C Q F l r hQ b c).app s ≫ _ = _
  rw [NerveBiparameterMaps.restriction_app]
  exact BinaryCotensor.glue_right (hQ (NerveSimplexStart.start s)) (b.app s) (c.app s)

include hQ in
lemma hom_ext {f g : NerveBiparameter.System Q F}
    (hl : f ≫ NerveBiparameterMaps.restriction B Q F l =
      g ≫ NerveBiparameterMaps.restriction B Q F l)
    (hr : f ≫ NerveBiparameterMaps.restriction C Q F r =
      g ≫ NerveBiparameterMaps.restriction C Q F r) : f = g := by
  apply NatTrans.ext
  funext s
  apply BinaryCotensor.hom_ext (hQ (NerveSimplexStart.start s))
  · exact congr_app hl s
  · exact congr_app hr s

end SerrePositivity.SimplicialModel.NerveBinaryBoundary
