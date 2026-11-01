module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanMonoStrictExtension

/-!
# 局所化で可逆な単射の実pushoutに沿って指定したKan値写像を延長する

## 概要
局所化で可逆な単射の実pushoutに沿って指定したKan値写像を延長する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
Kan値への実写像とホモトピー類のテストで比較射を調べる。
貼り合わせ・持ち上げとanodyne局所化の検出を使って像の可逆性を導く。

## 規約と注意
Kan条件・右持ち上げ性・単射性は各宣言で指定された範囲で用いる。
ここでのKan条件は外側も含む全hornの充填であり、内側hornだけの条件ではない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論の加法性・局所化で現れる貼り合わせと余極限の比較に利用できる。
[棚卸し m0424][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0424
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Prescribed Kan maps extend after an actual pushout of a localized mono

This proves strict extension and the surjective half of the Kan class
test. It does not assert injectivity or invertibility of the pushout map.
-/

@[expose] public section
universe v
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.KanMonoPushoutExtension
open HomotopyClasses
variable {A B C P K : SSet.{v}} (i : A ⟶ B) [Mono i]
  (j : A ⟶ C) (u : B ⟶ P) (g : C ⟶ P) (sq : IsPushout i j u g)
  (hi : IsIso (AnodyneHomotopy.anodyneQ.map i))
  (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))

include sq hi hK in
/-- 局所化で可逆な単射の実pushoutに沿って指定したKan値写像を延長する。

Kan条件・右持ち上げ性・単射性は各宣言で指定された範囲で用いる。
Kan値への実写像とホモトピー類のテストで比較射を調べる。
貼り合わせ・持ち上げとanodyne局所化の検出を使って像の可逆性を導く。
-/
lemma exists_extension (a : C ⟶ K) : ∃ b : P ⟶ K, g ≫ b = a := by
  obtain ⟨e, he⟩ := KanMonoStrictExtension.exists_extension i hK hi (j ≫ a)
  exact ⟨sq.desc e a he, sq.inr_desc e a he⟩

include sq hi hK in
lemma pre_surjective : Function.Surjective (pre g (K := K)) := by
  intro x
  obtain ⟨a, rfl⟩ := Quot.exists_rep x
  obtain ⟨b, hb⟩ := exists_extension i j u g sq hi hK a
  exact ⟨mk b, congrArg mk hb⟩

end SerrePositivity.SimplicialModel.KanMonoPushoutExtension
