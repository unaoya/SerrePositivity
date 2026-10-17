module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveBiparameterMaps
public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveNaturalBoundary

/-!
# 中断した任意モデル源への一般化：NerveBiparameterMapLaws

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Transport laws retaining canonical whole moving boundaries。

## 方針（定義・証明）
bar型の鎖パラメータと整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0462][inventory]を参照する。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0462
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Transport laws retaining canonical whole moving boundaries
-/

@[expose] public section
universe w uD vD uE vE
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalClosed
open SerrePositivity.NerveSimplexEndpoint

namespace SerrePositivity.SimplicialModel.NerveBiparameterMaps
variable {D : Type uD} [Category.{vD} D] (V K F G : D ⥤ SSet.{w})
  (i : V ⟶ K) (p : F ⟶ G)

lemma target_restriction : targetMap K F G p ≫ restriction V K G i =
    restriction V K F i ≫ targetMap V F G p := by
  apply NatTrans.ext
  funext s
  simp only [NatTrans.comp_app, restriction_app, targetMap_app]
  exact (pre_comm_ihom_map (i.app (NerveSimplexStart.start s)) (p.app (endpoint s))).symm

variable {E : Type uE} [Category.{vE} E] (H : E ⥤ D)

lemma reindex_restriction (a : NerveBiparameter.System K F) :
    reindex V F H (a ≫ restriction V K F i) = reindex K F H a ≫
      restriction (H ⋙ V) (H ⋙ K) (H ⋙ F) (Functor.whiskerLeft H i) := by
  apply NatTrans.ext
  funext s
  rfl

lemma reindex_natural (b : K ⟶ F) :
    reindex K F H (NerveNaturalBoundary.ofNatTrans K F b) =
      NerveNaturalBoundary.ofNatTrans (H ⋙ K) (H ⋙ F) (Functor.whiskerLeft H b) := by
  apply NatTrans.ext
  funext s
  rfl

lemma restrict_natural (b : K ⟶ F) :
    NerveNaturalBoundary.ofNatTrans K F b ≫ restriction V K F i =
      NerveNaturalBoundary.ofNatTrans V F (i ≫ b) := by
  apply NatTrans.ext
  funext s
  change (SSet.stdSimplex.isTerminalObj₀.from _ ≫ RelativeChoiceSpace.name
    (b.app (NerveSimplexStart.start s) ≫ F.map (NerveNaturalBoundary.whole s))) ≫
      (pre (i.app (NerveSimplexStart.start s))).app (F.obj (endpoint s)) = _
  apply (Category.assoc _ _ _).trans
  exact congrArg (fun e => SSet.stdSimplex.isTerminalObj₀.from _ ≫ e)
    ((RelativeChoiceSpace.name_precomp (i.app (NerveSimplexStart.start s))
      (b.app (NerveSimplexStart.start s) ≫ F.map (NerveNaturalBoundary.whole s))).trans
        (congrArg RelativeChoiceSpace.name (Category.assoc _ _ _).symm))

lemma mapTarget_natural (b : K ⟶ F) :
    NerveNaturalBoundary.ofNatTrans K F b ≫ targetMap K F G p =
      NerveNaturalBoundary.ofNatTrans K G (b ≫ p) := by
  apply NatTrans.ext
  funext s
  change (SSet.stdSimplex.isTerminalObj₀.from _ ≫ RelativeChoiceSpace.name
    (b.app (NerveSimplexStart.start s) ≫ F.map (NerveNaturalBoundary.whole s))) ≫
      (ihom (K.obj (NerveSimplexStart.start s))).map (p.app (endpoint s)) = _
  rw [Category.assoc, RelativeChoiceSpace.name_postcomp, Category.assoc,
    p.naturality, ← Category.assoc]
  rfl

end SerrePositivity.SimplicialModel.NerveBiparameterMaps
