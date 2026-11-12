module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordIntersection
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityColumn
public import Lean.Elab.Tactic.Omega

/-!
# 元の語の一列の削除

概要：指定した一列を削除した部分語と元の包含を構成する。
方針：元の列の有限集合から一つだけ除き、既存の部分語を使う。
規約：空語を含む長さの減少と、像の外の唯一の列を厳密に計算する。
使われ方：全行が恒等射の一列の基本縮約。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

namespace Word

def erase (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (j : Fin w.length) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subword w (Finset.univ.erase j)

def eraseInclusion (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (j : Fin w.length) : erase w j ⟶ w :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subwordInclusion w (Finset.univ.erase j)

lemma eraseInclusion_injective (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (j : Fin w.length) :
    Function.Injective (eraseInclusion w j).orderHom := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subwordInclusion_injective _ _

lemma erase_length (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (j : Fin w.length) : (erase w j).length = w.length - 1 := by
  simp only [erase, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subword, Finset.card_erase_of_mem (Finset.mem_univ j),
    Finset.card_univ, Fintype.card_fin]

lemma erase_length_lt (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (j : Fin w.length) : (erase w j).length < w.length := by
  rw [erase_length]
  have := j.isLt
  omega

lemma eraseInclusion_range (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (j : Fin w.length) :
    Set.range (eraseInclusion w j).orderHom = {j}ᶜ := by
  change Set.range (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subwordInclusion w (Finset.univ.erase j)).orderHom = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subwordInclusion_range]
  ext k
  simp only [Finset.mem_coe, Finset.mem_erase, Finset.mem_univ, and_true,
    Set.mem_compl_iff, Set.mem_singleton_iff]

lemma eraseInclusion_missing_iff (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (j k : Fin w.length) :
    (∀ i, (eraseInclusion w j).orderHom i ≠ k) ↔ k = j := by
  have hmem := congrArg (fun S : Set (Fin w.length) => k ∈ S) (eraseInclusion_range w j)
  simpa only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff, not_exists,
    not_not] using not_congr (iff_of_eq hmem)

end Word

lemma identityOutside_erase_iff {C : Type*} [Category* C] {W : MorphismProperty C}
    {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C} (R : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) (j : Fin w.length) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityOutside (Word.eraseInclusion w j) R ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityColumn R j := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityOutside
  simp only [Word.eraseInclusion_missing_iff, forall_eq]

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
