module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanTestDetection
public import Mathlib.AlgebraicTopology.SimplicialSet.Nonempty

/-!
# anodyne局所化で可逆な射は頂点の非空性を両方向に保存する

## 概要
anodyne局所化で可逆な射は頂点の非空性を両方向に保存する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
実写像または区間ホモトピーの関係を商へ降ろす。
代表元に依らないことを確認してから、誘導写像と比較を組み立てる。

## 規約と注意
Kan条件・右持ち上げ性・単射性は各宣言で指定された範囲で用いる。
ここでのKan条件は外側も含む全hornの充填であり、内側hornだけの条件ではない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0345][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0345
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Anodyne localization reflects nonemptiness of vertices

The empty simplicial set is a Kan test. No simplicial model structure is used.
-/

@[expose] public section
universe v
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.AnodyneNonempty

abbrev empty : SSet.{v} := (Functor.const SimplexCategoryᵒᵖ).obj PEmpty

lemma empty_kan : SSet.modelCategoryQuillen.J.rlp (terminal.from empty.{v}) := by
  apply (SSet.modelCategoryQuillen.fibration_iff _).mp
  apply SSet.KanComplex.iff.mpr
  intro n i f _
  obtain ⟨j, hj⟩ := exists_ne i
  exact PEmpty.elim ((f j hj).app (Opposite.op (SimplexCategory.mk 0))
    (SSet.stdSimplex.obj₀Equiv.symm 0))

lemma nonempty_of_localized_isIso {X Y : SSet.{v}} (f : X ⟶ Y)
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map f)) (hY : Y.Nonempty) : X.Nonempty := by
  by_contra hX
  have hs := (KanTestDetection.tests_of_anodyneQ_isIso f hf empty empty_kan).surjective
  obtain ⟨g, _⟩ := hs
    (HomotopyClasses.mk ((SSet.isInitialOfNotNonempty hX).to empty))
  obtain ⟨g, rfl⟩ := Quot.exists_rep g
  exact PEmpty.elim (g.app (Opposite.op (SimplexCategory.mk 0)) (Classical.choice hY))

/-- anodyne局所化で可逆な射は頂点の非空性を両方向に保存する。

Kan条件・右持ち上げ性・単射性は各宣言で指定された範囲で用いる。
実写像または区間ホモトピーの関係を商へ降ろす。
代表元に依らないことを確認してから、誘導写像と比較を組み立てる。
-/
lemma nonempty_iff_of_localized_isIso {X Y : SSet.{v}} (f : X ⟶ Y)
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map f)) : X.Nonempty ↔ Y.Nonempty :=
  ⟨fun hX => ⟨f.app _ (Classical.choice hX)⟩, nonempty_of_localized_isIso f hf⟩

end SerrePositivity.SimplicialModel.AnodyneNonempty
