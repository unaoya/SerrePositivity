module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordIntersection
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.IdentityColumn
public import Lean.Elab.Tactic.Omega

/-!
# 元の語の一列の削除

概要：指定した一列を削除した部分語と元の包含を構成する。
方針：元の列の有限集合から一つだけ除き、既存の部分語を使う。
規約：空語を含む長さの減少と、像の外の唯一の列を厳密に計算する。
使われ方：全行が恒等射の一列の基本縮約。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory

namespace Word

def erase (w : Word) (j : Fin w.length) : Word := subword w (Finset.univ.erase j)

def eraseInclusion (w : Word) (j : Fin w.length) : erase w j ⟶ w :=
  subwordInclusion w (Finset.univ.erase j)

lemma eraseInclusion_injective (w : Word) (j : Fin w.length) :
    Function.Injective (eraseInclusion w j).orderHom := subwordInclusion_injective _ _

lemma erase_length (w : Word) (j : Fin w.length) : (erase w j).length = w.length - 1 := by
  simp only [erase, subword, Finset.card_erase_of_mem (Finset.mem_univ j),
    Finset.card_univ, Fintype.card_fin]

lemma erase_length_lt (w : Word) (j : Fin w.length) : (erase w j).length < w.length := by
  rw [erase_length]
  have := j.isLt
  omega

lemma eraseInclusion_range (w : Word) (j : Fin w.length) :
    Set.range (eraseInclusion w j).orderHom = {j}ᶜ := by
  change Set.range (subwordInclusion w (Finset.univ.erase j)).orderHom = _
  rw [subwordInclusion_range]
  ext k
  simp only [Finset.mem_coe, Finset.mem_erase, Finset.mem_univ, and_true,
    Set.mem_compl_iff, Set.mem_singleton_iff]

lemma eraseInclusion_missing_iff (w : Word) (j k : Fin w.length) :
    (∀ i, (eraseInclusion w j).orderHom i ≠ k) ↔ k = j := by
  have hmem := congrArg (fun S : Set (Fin w.length) => k ∈ S) (eraseInclusion_range w j)
  simpa only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff, not_exists,
    not_not] using not_congr (iff_of_eq hmem)

end Word

lemma identityOutside_erase_iff {C : Type*} [Category* C] {W : MorphismProperty C}
    {w : Word} {X Y : C} (R : Zigzag W w X Y) (j : Fin w.length) :
    IdentityOutside (Word.eraseInclusion w j) R ↔ IdentityColumn R j := by
  unfold IdentityOutside
  simp only [Word.eraseInclusion_missing_iff, forall_eq]

end SerrePositivity.EInfinity.Hammock
