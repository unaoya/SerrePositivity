module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.GeneratorWordPath
public import Mathlib.Data.List.OfFn

/-!
# 元の文字列の射列の全合成

概要：文字列の圏の元の射列を、順序を保つ全隣接射の連結として回収する。
方針：元の始点からの射を終点の番号で帰納し、最後の一射を接続する。
規約：長さ零も含む元の全合成である。
使われ方：hammock の貼り戻しと残りの非指定文字列の同定。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C]

lemma composable_hom_flatten {n : ℕ} (F : ComposableArrows (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorFunctor.WordObject.{u, v} C) n) :
    F.hom = (List.ofFn (fun i : Fin n => F.map' i.val (i.val + 1))).flatten := by
  have hk : ∀ k (hk : k ≤ n), F.map' 0 k =
      (List.ofFn (fun i : Fin k => F.map' i.val (i.val + 1)
        (Nat.le_succ _) (by omega))).flatten := by
    intro k
    induction k with
    | zero =>
      intro _
      exact F.map_id _
    | succ k ih =>
      intro hkn
      rw [F.map'_comp 0 k (k + 1)]
      rw [List.ofFn_succ']
      change @List.append (Quiver.Total C) (F.map' 0 k) (F.map' k (k + 1)) = _
      rw [ih (Nat.le_of_succ_le hkn)]
      simp only [List.concat_eq_append, List.flatten_append, List.flatten_cons,
        List.flatten_nil, List.append_nil]
      rfl
  exact hk n le_rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
