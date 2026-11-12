module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoherentBarFaces
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoherentBarSubsetNaturality

/-!
概要：昇順部分集合のラベルを元の面・prefix・tail ラベルへ同定する。
方針：単射の像の列挙を使い、有限頂点の包含条件を直接照合する。
規約：各ラベルは元の単体的集合の等号として比較する。
使われ方：Bianchi の削除・左右切断と bar の係数の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
open scoped _root_.Simplicial
variable {I : SSet.{u}}

lemma dgCoherentBarSubsetLabel_image {m n : ℕ} (σ : I _⦋n⦌)
    (α : Fin (m + 1) →o Fin (n + 1)) (hα : Function.Injective α) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSubsetLabel σ (Finset.univ.image α) m
      (by rw [Finset.card_image_of_injective _ hα]; simp) =
      ⟨m, I.map (SimplexCategory.mkHom α).op σ⟩ := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSubsetLabel_map σ α hα Finset.univ m (by simp)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSubsetLabel_univ] at h
  exact h.symm

lemma dgCoherentBarSubsetLabel_face {n : ℕ} (σ : I _⦋n + 1⦌) (j : Fin (n + 2)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSubsetLabel σ (Finset.univ.erase j) n (by simp) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace σ j := by
  have him : Finset.univ.image j.succAboveOrderEmb.toOrderHom =
      (Finset.univ : Finset (Fin (n + 2))).erase j := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    exact Fin.exists_succAbove_eq_iff
  have h := dgCoherentBarSubsetLabel_image σ j.succAboveOrderEmb.toOrderHom
    j.succAboveOrderEmb.injective
  simpa only [him, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace, SimplicialObject.δ, SimplexCategory.δ] using h

lemma dgCoherentBarPrefixOrder_image (n : ℕ) (j : Fin (n + 1)) :
    Finset.univ.image (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixOrder n j.val (by omega)) =
      (Finset.univ : Finset (Fin (n + 1))).filter (· ≤ j) := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
  constructor
  · rintro ⟨i, rfl⟩
    change i.val ≤ j.val
    omega
  · intro hx
    refine ⟨⟨x.val, by change x.val ≤ j.val at hx; omega⟩, ?_⟩
    exact Fin.ext rfl

lemma dgCoherentBarTailOrder_image (n : ℕ) (j : Fin (n + 1)) :
    Finset.univ.image (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTailOrder n j.val (by omega)) =
      (Finset.univ : Finset (Fin (n + 1))).filter (j ≤ ·) := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
  constructor
  · rintro ⟨i, rfl⟩
    change j.val ≤ j.val + i.val
    omega
  · intro hx
    refine ⟨⟨x.val - j.val, by change j.val ≤ x.val at hx; omega⟩, ?_⟩
    apply Fin.ext
    change j.val + (x.val - j.val) = x.val
    change j.val ≤ x.val at hx
    omega

lemma dgCoherentBarPrefixOrder_injective (n k : ℕ) (h : k ≤ n) :
    Function.Injective (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixOrder n k h) := by
  intro a b hab
  have hv := congrArg Fin.val hab
  exact Fin.ext hv

lemma dgCoherentBarTailOrder_injective (n k : ℕ) (h : k ≤ n) :
    Function.Injective (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTailOrder n k h) := by
  intro a b hab
  apply Fin.ext
  have hv := congrArg Fin.val hab
  change k + a.val = k + b.val at hv
  omega


lemma dgCoherentBarPrefix_card (n : ℕ) (j : Fin (n + 1)) :
    ((Finset.univ : Finset (Fin (n + 1))).filter (· ≤ j)).card = j.val + 1 := by
  have hc := Finset.card_image_of_injective Finset.univ
    (dgCoherentBarPrefixOrder_injective n j.val (by omega))
  rw [dgCoherentBarPrefixOrder_image] at hc
  simpa only [Finset.card_univ, Fintype.card_fin] using hc

lemma dgCoherentBarTail_card (n : ℕ) (j : Fin (n + 1)) :
    ((Finset.univ : Finset (Fin (n + 1))).filter (j ≤ ·)).card = n - j.val + 1 := by
  have hc := Finset.card_image_of_injective Finset.univ
    (dgCoherentBarTailOrder_injective n j.val (by omega))
  rw [dgCoherentBarTailOrder_image] at hc
  simpa only [Finset.card_univ, Fintype.card_fin] using hc

lemma dgCoherentBarSubsetLabel_prefix {n : ℕ} (σ : I _⦋n⦌) (j : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSubsetLabel σ (Finset.univ.filter (· ≤ j)) j.val
      (dgCoherentBarPrefix_card n j) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefix σ j.val (by omega) := by
  have he := dgCoherentBarSubsetLabel_image σ
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixOrder n j.val (by omega))
    (dgCoherentBarPrefixOrder_injective n j.val (by omega))
  simpa only [dgCoherentBarPrefixOrder_image, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefix] using he

lemma dgCoherentBarSubsetLabel_tail {n : ℕ} (σ : I _⦋n⦌) (j : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSubsetLabel σ (Finset.univ.filter (j ≤ ·)) (n - j.val)
      (dgCoherentBarTail_card n j) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail σ j.val (by omega) := by
  have he := dgCoherentBarSubsetLabel_image σ
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTailOrder n j.val (by omega))
    (dgCoherentBarTailOrder_injective n j.val (by omega))
  simpa only [dgCoherentBarTailOrder_image, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail] using he

end SerrePositivity.InfinityCategories.Project.DerivedCategories
