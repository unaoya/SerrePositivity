module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct

/-!
# 指定した基底三角形の上で外側二次hornを充填する

## 概要
指定した基底三角形の上で外側二次hornを充填する。
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
[棚卸し m0440][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0440
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Fill a specified outer two-horn over its specified base triangle

Both given whole edges and the given base triangle are retained. Only
the original horn right lifting class is assumed, not a model structure.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
variable {E B : SSet.{v}} (p : E ⟶ B) (hp : SSet.modelCategoryQuillen.J.rlp p)

include hp in
/-- 指定した基底三角形の上で外側二次hornを充填する。

Kan条件・右持ち上げ性・単射性は各宣言で指定された範囲で用いる。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
lemma exists_triangle
    (e₀ e₁ : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ E)
    (b : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 2) ⟶ B)
    (hc : SSet.stdSimplex.δ (0 : Fin 2) ≫ e₀ = SSet.stdSimplex.δ (0 : Fin 2) ≫ e₁)
    (h₀ : e₀ ≫ p = SSet.stdSimplex.δ (0 : Fin 3) ≫ b)
    (h₁ : e₁ ≫ p = SSet.stdSimplex.δ (1 : Fin 3) ≫ b) :
    ∃ t : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 2) ⟶ E,
      SSet.stdSimplex.δ (0 : Fin 3) ≫ t = e₀ ∧
      SSet.stdSimplex.δ (1 : Fin 3) ≫ t = e₁ ∧ t ≫ p = b := by
  have : Fibration p := (SSet.modelCategoryQuillen.fibration_iff p).mpr hp
  let fs : ∀ (j : Fin 3) (_ : j ≠ 2),
      SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ E := fun j _ => if j = 0 then e₀ else e₁
  have hf : SSet.horn.IsCompatible fs := by
    intro j k hj hk hjk
    fin_cases j <;> fin_cases k <;> first
    | exact (hj rfl).elim
    | exact (hk rfl).elim
    | exact ((not_lt_of_ge (by decide)) hjk).elim
    | exact hc
  have hb : ∀ j hj, fs j hj ≫ p = SSet.stdSimplex.δ j ≫ b := by
    intro j hj
    fin_cases j <;> first | exact (hj rfl).elim | exact h₀ | exact h₁
  obtain ⟨t, ht, hb⟩ := hf.exists_lift p b hb
  exact ⟨t, ht 0 (by decide), ht 1 (by decide), hb⟩

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
