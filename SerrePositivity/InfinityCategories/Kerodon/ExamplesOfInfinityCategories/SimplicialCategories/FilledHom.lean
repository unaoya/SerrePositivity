module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.HornHollow
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PathDegeneracy

/-!
# 延長から全ての対象対の Hom 写像を復元する

概要：全区間の延長と真部分区間の回収から全ての対象対の Hom 写像を定義する。
方針：順序外の区間は空、真部分区間は既知の回収、全区間は延長を使う。
規約：延長の存在や性質は必要な定理で明示する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.10（Tag 00LT） の豊穣関手の構成。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.SimplicialThickening MonoidalCategory
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

variable {C : Type u} [Category.{v} C] [SimplicialCategory C]
variable {n : ℕ} {i : Fin (n + 3)}

/-- 概要：ホーンの充填用の Hom 写像を全ての頂点対に定義する。
方針：順序と真部分性で場合分けし、空の写像、標準回収、端点 Hom の延長を選ぶ。
規約：対象はホーンから回収した共通の対象族。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.10（Tag 00LT） の豊穣関手の Hom 成分。 -/
noncomputable def hornFillHom
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (h0 : 0 < i) (hn : i < Fin.last (n + 2))
    (g : nerve (Path (ULift.up.{v} (0 : Fin (n + 3)))
      (ULift.up (Fin.last (n + 2)))) ⟶
        SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ (Fin.last (n + 2))))
    (a b : Fin (n + 3)) : nerve (Path (ULift.up.{v} a) (ULift.up b)) ⟶
      SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ a) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ b) :=
  if hab : a ≤ b then
    if hp : a ≠ 0 ∨ b ≠ Fin.last (n + 2) then
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornProperIntervalHom σ h0 hn a b hab hp
    else by
      have ha : a = 0 := not_not.mp (fun h ↦ hp (Or.inl h))
      have hb : b = Fin.last (n + 2) := not_not.mp (fun h ↦ hp (Or.inr h))
      subst a b
      exact g
  else _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathEmptyHom (ULift.up a) (ULift.up b) hab _

/-- 概要：順序付けられた真部分区間で充填用の Hom は標準回収に等しい。
方針：定義の二つの分岐を選ぶ。
規約：比較は共通の対象間の厳密な等式。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.10（Tag 00LT） の既知区間の回収。 -/
lemma hornFillHom_proper
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (h0 : 0 < i) (hn : i < Fin.last (n + 2)) (g) (a b : Fin (n + 3))
    (hab : a ≤ b) (hp : a ≠ 0 ∨ b ≠ Fin.last (n + 2)) :
    hornFillHom σ h0 hn g a b = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornProperIntervalHom σ h0 hn a b hab hp := by
  simp only [hornFillHom, dite_eq_left hab, dite_eq_left hp]

/-- 概要：全区間で充填用の Hom は与えた延長に等しい。
方針：両端点の順序と真部分性の否定で定義を計算する。
規約：延長に整合性の仮定は不要。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.10（Tag 00LT） の新しい Hom の成分。 -/
lemma hornFillHom_full
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (h0 : 0 < i) (hn : i < Fin.last (n + 2)) (g) :
    hornFillHom σ h0 hn g 0 (Fin.last (n + 2)) = g := by
  simp only [hornFillHom, Fin.zero_le, dite_true, ne_self_iff_false, or_self, dite_false]

/-- 概要：充填用の Hom は全ての豊穣単位を保つ。
方針：同じ端点の区間は真部分区間なので標準回収の単位則へ帰着する。
規約：端点 Hom の延長の性質を要求しない。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.10（Tag 00LT） の豊穣関手の単位則。 -/
lemma hornFillHom_id
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (h0 : 0 < i) (hn : i < Fin.last (n + 2)) (g) (a : Fin (n + 3)) :
    eId SSet (SimplicialThickening.mk (ULift.up.{v} a)) ≫
      hornFillHom σ h0 hn g a a = eId SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ a) := by
  have hp : a ≠ 0 ∨ a ≠ Fin.last (n + 2) := by
    by_cases ha : a = 0
    · subst a
      exact Or.inr (ne_of_lt (h0.trans hn))
    · exact Or.inl ha
  rw [hornFillHom_proper σ h0 hn g a a le_rfl hp]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornProperIntervalHom_id σ h0 hn a hp

/-- 概要：全区間の内部切断点を経由する合成について充填用の Hom は合成を保つ。
方針：既知の合成面を固定する延長の条件と合成面への同型を使う。
規約：延長の面への制限の条件は実際の Kan 延長が満たすもの。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.10（Tag 00LT） の新しい Hom に関する合成則。 -/
lemma hornFillHom_comp_inner
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (h0 : 0 < i) (hn : i < Fin.last (n + 2)) (g)
    (hg : ∀ j, (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathHollowFace (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHollowPoint.{v} i h0 hn) j).ι ≫ g =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHollowFaceHom σ h0 hn j)
    (b : Fin (n + 3)) (hb0 : 0 < b) (hbn : b < Fin.last (n + 2)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up.{v} (0 : Fin (n + 3))) (ULift.up b)
      (ULift.up (Fin.last (n + 2))) ≫ hornFillHom σ h0 hn g 0 (Fin.last (n + 2)) =
    (hornFillHom σ h0 hn g 0 b ⊗ₘ hornFillHom σ h0 hn g b (Fin.last (n + 2))) ≫
      SimplicialCategory.sHomComp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ b)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj σ (Fin.last (n + 2))) := by
  rw [hornFillHom_full,
    hornFillHom_proper σ h0 hn g 0 b (Fin.zero_le b) (Or.inr (ne_of_lt hbn)),
    hornFillHom_proper σ h0 hn g b (Fin.last (n + 2)) (Fin.le_last b)
      (Or.inl (ne_of_gt hb0))]
  have hb := hg (.inl ⟨ULift.up.{v} b, hb0, hbn⟩)
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up.{v} b)).ι ≫ g =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornInnerCompositionHom σ h0 hn b hb0 hbn at hb
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThroughIso_hom_ι, Category.assoc, hb]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornCompositionHom_on_product σ h0 hn 0 b (Fin.last (n + 2))
    (Fin.zero_le b) (Fin.le_last b) (Or.inr (ne_of_lt hbn)) (Or.inl (ne_of_gt hb0))

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
