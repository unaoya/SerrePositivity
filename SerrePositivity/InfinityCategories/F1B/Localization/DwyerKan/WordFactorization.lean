module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordMerge
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordPuncture
public import Mathlib.Order.Hom.Set

/-!
# 元の語の写像の基本操作への因子分解

概要：隣接等像は基本合成で、欠けた列は一列包含で元の写像から分離できる。
方針：Fin の隣接単射判定と、包含の像への順序同型を使う。
規約：元の語の色と元の写像への厳密な因子分解を保持する。
使われ方：全語の遷移に対する正規形の不変性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock.Word
open CategoryTheory

/-- 元の像に入る写像を、単射な元の語の写像を通して持ち上げる。 -/
def factorEmbedding {a b c : Word} (e : a ⟶ b) (he : Function.Injective e.orderHom)
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
  exact ⟨g, hom_ext _ _ hh⟩

lemma adjacent_color_of_image_eq {k : ℕ} (d : Fin (k + 2) → Direction) {b : Word}
    (f : (⟨k + 2, d⟩ : Word) ⟶ b) (p : Fin (k + 1))
    (hp : f.orderHom p.castSucc = f.orderHom p.succ) : d p.castSucc = d p.succ :=
  (f.direction_eq p.castSucc).symm.trans
    ((congrArg b.direction hp).trans (f.direction_eq p.succ))

/-- 元の隣接等像の二列を先に合成する、厳密な因子分解。 -/
def factorMerge {k : ℕ} (d : Fin (k + 2) → Direction) {b : Word}
    (f : (⟨k + 2, d⟩ : Word) ⟶ b) (p : Fin (k + 1))
    (hp : f.orderHom p.castSucc = f.orderHom p.succ) :
    {g : mergeTarget d p ⟶ b // mergeMap d p (adjacent_color_of_image_eq d f p hp) ≫ g = f} := by
  let g : mergeTarget d p ⟶ b :=
    { orderHom := f.orderHom.comp (Fin.succAboveOrderEmb p.succ).toOrderHom
      direction_eq i := f.direction_eq (p.succ.succAbove i) }
  refine ⟨g, hom_ext _ _ ?_⟩
  intro i
  change f.orderHom (p.succ.succAbove (p.predAbove i)) = f.orderHom i
  by_cases hi : i = p.succ
  · subst i
    rw [Fin.predAbove_succ_self, Fin.succAbove_succ_self]
    exact hp
  · rw [Fin.succ_succAbove_predAbove hi]

end SerrePositivity.EInfinity.Hammock.Word
