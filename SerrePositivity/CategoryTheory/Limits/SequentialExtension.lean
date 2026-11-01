module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.Preorder.Basic

/-!
# 整合的な逐次延長族から余極限上の射を構成する

## 概要
整合的な逐次延長族から余極限上の射を構成する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
前段を保持する延長を逐次的に選び、整合的な余錐を作る。
余極限の普遍射で全体へ降下させ、各段階への制限を確認する。

## 規約と注意
各段階の延長が前段を保持し、指定した余極限が存在することを仮定する。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はS-構成に現れる圏のnerve、射列、図式間の自然なホモトピーに利用できる。
[棚卸し m0011][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0011
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Successively chosen extensions and their colimit

Each stage is chosen from extensions of the preceding stage, rather than
chosen independently. The resulting cocone retains every earlier choice.
This construction is independent of model structures and universe equality.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SequentialExtension

variable {C : Type u} [Category.{v} C] (F : ℕ ⥤ C) (P : C)
  (extend : ∀ n (a : F.obj n ⟶ P),
    {b : F.obj (n + 1) ⟶ P // F.map (homOfLE (Nat.le_succ n)) ≫ b = a})
  (a₀ : F.obj 0 ⟶ P)

/-- The next map extends the actual map selected at the preceding stage. -/
def stage : ∀ n, F.obj n ⟶ P
  | 0 => a₀
  | n + 1 => (extend n (stage n)).val

lemma stage_zero : stage F P extend a₀ 0 = a₀ := rfl

@[reassoc]
lemma stage_succ (n : ℕ) :
    F.map (homOfLE (Nat.le_succ n)) ≫ stage F P extend a₀ (n + 1) =
      stage F P extend a₀ n :=
  (extend n (stage F P extend a₀ n)).property

def cocone : Cocone F where
  pt := P
  ι := NatTrans.ofSequence (stage F P extend a₀) (by
    intro n
    simpa using stage_succ F P extend a₀ n)

@[reassoc]
lemma stage_map {n m : ℕ} (f : n ⟶ m) :
    F.map f ≫ stage F P extend a₀ m = stage F P extend a₀ n := by
  exact (cocone F P extend a₀).w f

/-- 整合的な逐次延長族から余極限上の射を構成する。

各段階の延長が前段を保持し、指定した余極限が存在することを仮定する。
前段を保持する延長を逐次的に選び、整合的な余錐を作る。
余極限の普遍射で全体へ降下させ、各段階への制限を確認する。
-/
def descend (c : Cocone F) (hc : IsColimit c) : c.pt ⟶ P :=
  hc.desc (cocone F P extend a₀)

@[reassoc]
lemma descend_stage (c : Cocone F) (hc : IsColimit c) (n : ℕ) :
    c.ι.app n ≫ descend F P extend a₀ c hc = stage F P extend a₀ n :=
  hc.fac (cocone F P extend a₀) n

lemma descend_zero (c : Cocone F) (hc : IsColimit c) :
    c.ι.app 0 ≫ descend F P extend a₀ c hc = a₀ :=
  descend_stage F P extend a₀ c hc 0

end SerrePositivity.SequentialExtension
