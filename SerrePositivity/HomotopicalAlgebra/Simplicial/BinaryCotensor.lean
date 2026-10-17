module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.BoundaryCotensor
public import SerrePositivity.HomotopicalAlgebra.Simplicial.BoundaryOneCotensor

/-!
# 二つの余テンソル族を実際の二項余積上に貼り合わせる

## 概要
二つの余テンソル族を実際の二項余積上に貼り合わせる。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0349][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0349
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Gluing whole cotensor families on an actual binary coproduct
-/

@[expose] public section
universe w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalClosed
open SerrePositivity.SimplicialModel.BoundaryCotensor

namespace SerrePositivity.SimplicialModel.BinaryCotensor
variable {B C Q T P : SSet.{w}} {l : B ⟶ Q} {r : C ⟶ Q}
  (hQ : IsColimit (BinaryCofan.mk l r)) (b : T ⟶ (ihom B).obj P) (c : T ⟶ (ihom C).obj P)

/-- 二つの余テンソル族を実際の二項余積上に貼り合わせる。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
def glue : T ⟶ (ihom Q).obj P :=
  transpose (hQ.desc (BinaryCofan.mk (transpose b) (transpose c)))

@[reassoc]
lemma glue_left : glue hQ b c ≫ (pre l).app P = b := by
  apply transpose_injective
  rw [transpose_restriction, glue, transpose_transpose]
  exact hQ.fac (BinaryCofan.mk (transpose b) (transpose c)) ⟨WalkingPair.left⟩

@[reassoc]
lemma glue_right : glue hQ b c ≫ (pre r).app P = c := by
  apply transpose_injective
  rw [transpose_restriction, glue, transpose_transpose]
  exact hQ.fac (BinaryCofan.mk (transpose b) (transpose c)) ⟨WalkingPair.right⟩

include hQ in
lemma hom_ext {f g : T ⟶ (ihom Q).obj P}
    (hl : f ≫ (pre l).app P = g ≫ (pre l).app P)
    (hr : f ≫ (pre r).app P = g ≫ (pre r).app P) : f = g := by
  apply transpose_injective
  apply hQ.hom_ext
  intro j
  rcases j with ⟨j⟩
  cases j
  · exact (transpose_restriction l f).symm.trans
      ((congrArg transpose hl).trans (transpose_restriction l g))
  · exact (transpose_restriction r f).symm.trans
      ((congrArg transpose hr).trans (transpose_restriction r g))

end SerrePositivity.SimplicialModel.BinaryCotensor
