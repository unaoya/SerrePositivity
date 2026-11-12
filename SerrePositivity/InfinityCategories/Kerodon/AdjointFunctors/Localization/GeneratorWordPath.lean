module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorFunctor
public import Mathlib.CategoryTheory.ComposableArrows.Basic

/-!
# 元の非指定文字列の射列の空性

概要：文字列の圏での全合成が空である条件を元の全隣接射で判定する。
方針：元の射列の分割と文字列の連結の空性を使う。
規約：長さ零と等式による端点移送も含む。
使われ方：元の hammock の非空文字列と非空列の同定。

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

lemma word_eqToHom {X Y : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorFunctor.WordObject.{u, v} C} (h : X = Y) :
    (eqToHom h : X ⟶ Y) = [] := by
  cases h
  rfl

lemma erase_transport (W : MorphismProperty C) {A A' B B' : Paths C}
    (hA : A' = A) (hB : B = B') (p : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.erase W (eqToHom hA ≫ p ≫ eqToHom hB) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.erase W p := by
  cases hA
  cases hB
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

lemma composable_hom_eq_nil_iff {n : ℕ} (F : ComposableArrows (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorFunctor.WordObject.{u, v} C) n) :
    F.hom = [] ↔ ∀ i : Fin n, F.map' i.val (i.val + 1) = [] := by
  constructor
  · intro h i
    change F.map' 0 n = [] at h
    rw [F.map'_comp 0 i.val n, F.map'_comp i.val (i.val + 1) n] at h
    change _ ++ (_ ++ _) = [] at h
    exact (List.append_eq_nil_iff.1 (List.append_eq_nil_iff.1 h).2).1
  · intro h
    have hk : ∀ k (hk : k ≤ n), F.map' 0 k = [] := by
      intro k
      induction k with
      | zero =>
        intro _
        exact F.map_id _
      | succ k ih =>
        intro hkn
        rw [F.map'_comp 0 k (k + 1)]
        rw [ih (Nat.le_of_succ_le hkn), h ⟨k, Nat.lt_of_succ_le hkn⟩]
        rfl
    exact hk n le_rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
