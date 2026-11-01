module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneKanReplacement
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanHomotopyClasses

/-!
# anodyne局所化での可逆性は全Kan値ホモトピー類のテストで判定できる

## 概要
anodyne局所化での可逆性は全Kan値ホモトピー類のテストで判定できる。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
実写像または区間ホモトピーの関係を商へ降ろす。
代表元に依らないことを確認してから、誘導写像と比較を組み立てる。

## 規約と注意
テスト対象は外側を含む全hornを充填するKan複体であり、値モデルは入力しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0437][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0437
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Model-free detection of anodyne localization by all Kan-valued homotopy tests

The proof uses only the actual horn replacement and its anodyne unit.
It applies in any value universe without installing a model structure.
-/

@[expose] public section
universe v uH vH
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.KanTestDetection
open HomotopyClasses
variable {X Y : SSet.{v}} (f : X ⟶ Y)

abbrev Tests : Prop := ∀ (K : SSet.{v}),
  SSet.modelCategoryQuillen.J.rlp (terminal.from K) → Function.Bijective (pre f (K := K))

lemma replacement_pre_square (K : SSet.{v}) :
    pre (AnodyneKanReplacement.unit.app X) (K := K) ∘
      pre (AnodyneKanReplacement.functor.map f) =
        pre f ∘ pre (AnodyneKanReplacement.unit.app Y) := by
  funext t
  refine Quot.inductionOn t (fun g => ?_)
  change mk (AnodyneKanReplacement.unit.app X ≫
      (AnodyneKanReplacement.functor.map f ≫ g)) =
    mk (f ≫ (AnodyneKanReplacement.unit.app Y ≫ g))
  have h : AnodyneKanReplacement.unit.app X ≫ AnodyneKanReplacement.functor.map f =
      f ≫ AnodyneKanReplacement.unit.app Y := (AnodyneKanReplacement.unit.naturality f).symm
  rw [← Category.assoc, h, Category.assoc]

lemma replacement_tests (hf : Tests f) : Tests (AnodyneKanReplacement.functor.map f) := by
  intro K hK
  have hX := KanHomotopyClasses.pre_bijective (AnodyneKanReplacement.unit.app X)
    (AnodyneKanReplacement.unit_anodyne X) hK
  have hY := KanHomotopyClasses.pre_bijective (AnodyneKanReplacement.unit.app Y)
    (AnodyneKanReplacement.unit_anodyne Y) hK
  apply (Function.Bijective.of_comp_iff' hX _).mp
  rw [replacement_pre_square]
  exact (hf K hK).comp hY

variable {H : Type uH} [Category.{vH} H] (L : SSet.{v} ⥤ H)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

include hL in
/-- 全Kan値のホモトピー類テストからanodyne局所化像の可逆性を導く。

テスト対象は外側を含む全hornを充填するKan複体であり、値モデルは入力しない。
実写像または区間ホモトピーの関係を商へ降ろす。
代表元に依らないことを確認してから、誘導写像と比較を組み立てる。
-/
lemma map_isIso_of_tests (hf : Tests f) : IsIso (L.map f) := by
  have hr := replacement_tests f hf
  have : IsIso (L.map (AnodyneKanReplacement.functor.map f)) :=
    HomotopyClasses.map_isIso_of_tests L hL _
      (hr _ (AnodyneKanReplacement.terminal_rlp X)).surjective
      (hr _ (AnodyneKanReplacement.terminal_rlp Y)).injective
  have : IsIso (L.map (AnodyneKanReplacement.unit.app X)) :=
    hL _ (AnodyneKanReplacement.unit_anodyne X)
  have : IsIso (L.map (AnodyneKanReplacement.unit.app Y)) :=
    hL _ (AnodyneKanReplacement.unit_anodyne Y)
  have h := congrArg L.map (AnodyneKanReplacement.unit.naturality f)
  rw [L.map_comp, L.map_comp] at h
  have : IsIso (L.map f ≫ L.map (AnodyneKanReplacement.unit.app Y)) := h.symm ▸ inferInstance
  exact (isIso_comp_right_iff _ _).mp this

lemma tests_of_anodyneQ_isIso (hf : IsIso (AnodyneHomotopy.anodyneQ.map f)) : Tests f := by
  intro K hK
  have h := AnodyneHomotopy.map_isIso_of_anodyneQ_isIso
    (HomotopyClasses.functor K).rightOp (KanHomotopyClasses.rightOp_inverts K hK) f hf
  have : IsIso ((HomotopyClasses.functor K).map f.op) := (isIso_op_iff _).mp h
  exact (isIso_iff_bijective _).mp this

/-- anodyne局所化での可逆性は全Kan値ホモトピー類のテストで判定できる。

テスト対象は外側を含む全hornを充填するKan複体であり、値モデルは入力しない。
実写像または区間ホモトピーの関係を商へ降ろす。
代表元に依らないことを確認してから、誘導写像と比較を組み立てる。
-/
lemma anodyneQ_isIso_iff_tests : IsIso (AnodyneHomotopy.anodyneQ.map f) ↔ Tests f :=
  ⟨tests_of_anodyneQ_isIso f, map_isIso_of_tests f AnodyneHomotopy.anodyneQ
    (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions)⟩

end SerrePositivity.SimplicialModel.KanTestDetection
