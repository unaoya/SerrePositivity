module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanRestrictionLifting
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanPostDetection
public import SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexParameterHom

/-!
# 局所化可逆な射に沿うKan値内部Homの制限も局所化可逆となる

## 概要
局所化可逆な射に沿うKan値内部Homの制限も局所化可逆となる。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。

## 規約と注意
制限する射の局所化可逆性と値のKan性を仮定し、制限射自体の単射性は要求しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0433][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0433
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Internal Hom restriction along any localized equivalence is a localized equivalence

Neither a monomorphism nor a model structure is required.
-/

@[expose] public section
universe v
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.KanRestrictionEquivalence
variable {A B K : SSet.{v}} (a : A ⟶ B)
  (ha : IsIso (AnodyneHomotopy.anodyneQ.map a))
  (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))

include ha hK in
/-- 局所化可逆な射に沿うKan値内部Homの制限も局所化可逆となる。

制限する射の局所化可逆性と値のKan性を仮定し、制限射自体の単射性は要求しない。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
lemma localized_isIso : IsIso (AnodyneHomotopy.anodyneQ.map ((pre a).app K)) :=
  KanPostDetection.localized_isIso _ (SimplexParameterHom.native_kan B K hK)
    (SimplexParameterHom.native_kan A K hK)
    (KanRestrictionLifting.post_bijective a ha hK _).surjective
    (KanRestrictionLifting.post_bijective a ha hK _).injective

end SerrePositivity.SimplicialModel.KanRestrictionEquivalence
