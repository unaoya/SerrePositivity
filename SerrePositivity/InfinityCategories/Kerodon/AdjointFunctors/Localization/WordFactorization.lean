module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordMerge
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordPuncture
public import Mathlib.Order.Hom.Set

/-!
# 元の語の写像の基本操作への因子分解

概要：隣接等像は基本合成で、欠けた列は一列包含で元の写像から分離できる。
方針：Fin の隣接単射判定と、包含の像への順序同型を使う。
規約：元の語の色と元の写像への厳密な因子分解を保持する。
使われ方：全語の遷移に対する正規形の不変性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

/-- 元の像に入る写像を、単射な元の語の写像を通して持ち上げる。 -/
def factorEmbedding {a b c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (e : a ⟶ b) (he : Function.Injective e.orderHom)
    (f : c ⟶ b) (hRange : Set.range f.orderHom ⊆ Set.range e.orderHom) :
    {g : c ⟶ a // g ≫ e = f} := by
  let ee := (e.orderHom.monotone.strictMono_of_injective he).orderIso e.orderHom
  let h : Fin c.length →o Fin a.length :=
    { toFun i := ee.symm ⟨f.orderHom i, hRange ⟨i, rfl⟩⟩
      monotone' _ _ hij := ee.symm.monotone (f.orderHom.monotone hij) }
  have hh (i : Fin c.length) : e.orderHom (h i) = f.orderHom i :=
    congrArg Subtype.val (ee.apply_symm_apply ⟨f.orderHom i, hRange ⟨i, rfl⟩⟩)
  let g : c ⟶ a :=
    { orderHom := h
      direction_eq i := (e.direction_eq (h i)).symm.trans
        ((congrArg b.direction (hh i)).trans (f.direction_eq i)) }
  exact ⟨g, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.hom_ext _ _ hh⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (factorEmbedding)


lemma adjacent_color_of_image_eq {k : ℕ} (d : Fin (k + 2) → _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) {b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word}
    (f : (⟨k + 2, d⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) ⟶ b) (p : Fin (k + 1))
    (hp : f.orderHom p.castSucc = f.orderHom p.succ) : d p.castSucc = d p.succ :=
  (f.direction_eq p.castSucc).symm.trans
    ((congrArg b.direction hp).trans (f.direction_eq p.succ))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (adjacent_color_of_image_eq)


/-- 元の隣接等像の二列を先に合成する、厳密な因子分解。 -/
def factorMerge {k : ℕ} (d : Fin (k + 2) → _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) {b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word}
    (f : (⟨k + 2, d⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) ⟶ b) (p : Fin (k + 1))
    (hp : f.orderHom p.castSucc = f.orderHom p.succ) :
    {g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeTarget d p ⟶ b // _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeMap d p (adjacent_color_of_image_eq d f p hp) ≫ g = f} := by
  let g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeTarget d p ⟶ b :=
    { orderHom := f.orderHom.comp (Fin.succAboveOrderEmb p.succ).toOrderHom
      direction_eq i := f.direction_eq (p.succ.succAbove i) }
  refine ⟨g, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.hom_ext _ _ ?_⟩
  intro i
  change f.orderHom (p.succ.succAbove (p.predAbove i)) = f.orderHom i
  by_cases hi : i = p.succ
  · subst i
    rw [Fin.predAbove_succ_self, Fin.succAbove_succ_self]
    exact hp
  · rw [Fin.succ_succAbove_predAbove hi]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (factorMerge)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
