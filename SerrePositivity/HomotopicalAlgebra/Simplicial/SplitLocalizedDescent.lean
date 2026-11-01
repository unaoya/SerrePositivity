module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneLocalizedTensor
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanLocalizedRepresentatives

/-!
# 分裂した局所化同値に沿うKan値ホモトピーの降下をテンソル付きの族に拡張する

## 概要
分裂した局所化同値に沿うKan値ホモトピーの降下をテンソル付きの族に拡張する。
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
[棚卸し m0578][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0578
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Descending maps into Kan targets along a split localized equivalence

The descended map and the comparison interval are actual simplicial maps.
This is descent of an individual family; no composition or higher coherent
selection of the comparison intervals is asserted.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace SerrePositivity.SimplicialModel.SplitLocalizedDescent
variable {A B K : SSet.{v}} {a : A ⟶ B} (s : SplitEpi a)
  (ha : IsIso (AnodyneHomotopy.anodyneQ.map a))

abbrev descend (h : A ⟶ K) : B ⟶ K := s.section_ ≫ h

include ha in
lemma localized_retraction : AnodyneHomotopy.anodyneQ.map (a ≫ s.section_) =
    AnodyneHomotopy.anodyneQ.map (𝟙 A) := by
  let Q := AnodyneHomotopy.anodyneQ.{v}
  have := ha
  have hs : Q.map s.section_ ≫ Q.map a = 𝟙 _ := by
    rw [← Q.map_comp, s.id, Q.map_id]
  rw [Q.map_comp, Q.map_id]
  apply (cancel_mono (Q.map a)).mp
  rw [Category.assoc, hs, Category.comp_id, Category.id_comp]

include ha in
lemma descend_map (h : A ⟶ K) :
    AnodyneHomotopy.anodyneQ.map (a ≫ descend s h) =
      AnodyneHomotopy.anodyneQ.map h := by
  rw [descend, ← Category.assoc, AnodyneHomotopy.anodyneQ.map_comp,
    localized_retraction s ha, AnodyneHomotopy.anodyneQ.map_id, Category.id_comp]

include ha in
lemma descend_homotopy (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K)) (h : A ⟶ K) :
    Nonempty (SSet.Homotopy (a ≫ descend s h) h) :=
  (KanLocalizedRepresentatives.map_eq_iff_homotopy AnodyneHomotopy.anodyneQ hK _ _).mp
    (descend_map s ha h)

include ha in
lemma lifts_homotopy {T : SSet.{v}} (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))
    (h : A ⟶ K) (f g : T ⟶ A) (hfg : f ≫ a = g ≫ a) :
    Nonempty (SSet.Homotopy (f ≫ h) (g ≫ h)) := by
  let Q := AnodyneHomotopy.anodyneQ.{v}
  have := ha
  have he : Q.map f = Q.map g := by
    apply (cancel_mono (Q.map a)).mp
    rw [← Q.map_comp, ← Q.map_comp, hfg]
  apply (KanLocalizedRepresentatives.map_eq_iff_homotopy Q hK _ _).mp
  simp only [Q.map_comp, he]

/-- This split epi still concerns Hom parameters, not a section of categories. -/
def tensorSplit (P : SSet.{v}) : SplitEpi (P ◁ a) where
  section_ := P ◁ s.section_
  id := by
    change (tensorLeft P).map s.section_ ≫ (tensorLeft P).map a = 𝟙 _
    rw [← (tensorLeft P).map_comp, s.id, (tensorLeft P).map_id]

include ha in
/-- 分裂した局所化同値に沿うKan値ホモトピーの降下をテンソル付きの族に拡張する。

Kan条件・右持ち上げ性・単射性は各宣言で指定された範囲で用いる。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
lemma tensor_descend_homotopy (P : SSet.{v})
    (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K)) (h : P ⊗ A ⟶ K) :
    Nonempty (SSet.Homotopy ((P ◁ a) ≫ descend (tensorSplit s P) h) h) :=
  descend_homotopy (tensorSplit s P)
    (AnodyneHomotopy.whiskerLeft_anodyneQ_isIso a ha P) hK h

end SerrePositivity.SimplicialModel.SplitLocalizedDescent
