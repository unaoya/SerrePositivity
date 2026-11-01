module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanRestrictionLifting
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanRelativeLifting

/-!
# 局所化で可逆な単射に沿って両端点を保つKan値ホモトピーを延長する

## 概要
局所化で可逆な単射に沿って両端点を保つKan値ホモトピーを延長する。
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
[棚卸し m0425][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0425
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Homotopy extension with both specified endpoints along a localized mono

The entire original homotopy on the subobject is retained. Restriction
lifting is transported through the actual tensor/internal-Hom adjunction.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.KanMonoRelativeHomotopy
variable {A B K : SSet.{v}} (i : A ⟶ B) [Mono i]
  (hi : IsIso (AnodyneHomotopy.anodyneQ.map i))
  (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))

include hi hK in
/-- 局所化で可逆な単射に沿って両端点を保つKan値ホモトピーを延長する。

Kan条件・右持ち上げ性・単射性は各宣言で指定された範囲で用いる。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
lemma exists_extension (f g : B ⟶ K) (H : SSet.Homotopy (i ≫ f) (i ≫ g)) :
    ∃ V : SSet.Homotopy f g,
      i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ V.h = H.h := by
  let pp := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{v}) i
    (SSet.boundary 1).ι
  have hr : HasLiftingProperty (SSet.boundary.{v} 1).ι
      ((CategoryTheory.MonoidalClosed.pre i).app K) :=
    KanRestrictionLifting.all_mono_rlp i hi hK _ inferInstance
  have hl : HasLiftingProperty pp.ι (terminal.from K) :=
    (CategoryTheory.MonoidalClosed.internalHomAdjunction₂.hasLiftingProperty_iff pp
      (Functor.PullbackObjObj.ofIsTerminal CategoryTheory.MonoidalClosed.internalHom
        i (terminal.from K) terminalIsTerminal)).mpr hr
  exact KanRelativeLifting.exists_extension i hl f g H

end SerrePositivity.SimplicialModel.KanMonoRelativeHomotopy
