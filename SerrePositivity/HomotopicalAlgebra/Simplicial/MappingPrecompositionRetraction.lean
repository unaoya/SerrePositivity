module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.PrecompositionHomotopy
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanPullbackDeformation

/-!
# 基底上の強変形レトラクトを内部Homへ移しそのpullbackの局所化可逆性を導く

## 概要
基底上の強変形レトラクトを内部Homへ移しそのpullbackの局所化可逆性を導く。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。

## 規約と注意
Kan条件・右持ち上げ性・単射性は各宣言で指定された範囲で用いる。
ここでのKan条件は外側も含む全hornの充填であり、内側hornだけの条件ではない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0450][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0450
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# A vertical retraction homotopy becomes a strong mapping-space deformation retract

The actual precomposition inclusion is fixed on its entire interval.
This supplies the exact hypothesis needed for Kan pullback deformation,
without replacing any mapping space or assuming a value model structure.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.MappingPrecompositionRetraction
variable {E B : SSet.{v}} (p : E ⟶ B) (s : B ⟶ E) (hs : s ≫ p = 𝟙 B)
  (H : SSet.Homotopy (𝟙 E) (p ≫ s))
  (hH : H.h ≫ p = fst E (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ p)

include hs in
lemma retraction (K : SSet.{v}) :
    (MonoidalClosed.pre p).app K ≫ (MonoidalClosed.pre s).app K = 𝟙 _ := by
  rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map, hs, MonoidalClosed.pre_id]
  rfl

def homotopy (K : SSet.{v}) :
    SSet.Homotopy (𝟙 ((ihom E).obj K))
      ((MonoidalClosed.pre s).app K ≫ (MonoidalClosed.pre p).app K) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints (PrecompositionHomotopy.homotopy H K)
    (by rw [MonoidalClosed.pre_id]; rfl)
    (by rw [MonoidalClosed.pre_map]; rfl)

include hH in
lemma fixed (K : SSet.{v}) :
    ((MonoidalClosed.pre p).app K) ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫
      (homotopy p s H K).h =
    fst ((ihom B).obj K) (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫
      (MonoidalClosed.pre p).app K := by
  rw [homotopy, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints_h]
  change _ ≫ PrecompositionHomotopy.interval H K = _
  rw [PrecompositionHomotopy.interval_post]
  exact PrecompositionHomotopy.interval_constant (HomotopyClasses.postHomotopy p H) K p hH

include hs hH in
/-- 基底上の強変形レトラクトを内部Homへ移しそのpullbackの局所化可逆性を導く。

Kan条件・右持ち上げ性・単射性は各宣言で指定された範囲で用いる。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
lemma pullback_localized_isIso (K : SSet.{v}) {Z P : SSet.{v}}
    (q : Z ⟶ (ihom E).obj K) (hq : SSet.modelCategoryQuillen.J.rlp q)
    (j : P ⟶ Z) (k : P ⟶ (ihom B).obj K)
    (sq : IsPullback j k q ((MonoidalClosed.pre p).app K)) :
    IsIso (AnodyneHomotopy.anodyneQ.map j) :=
  KanPullbackDeformation.localized_isIso _ _ (retraction p s hs K)
    (homotopy p s H K) (fixed p s H hH K) q hq j k sq

end SerrePositivity.SimplicialModel.MappingPrecompositionRetraction
