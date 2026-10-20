module

public import SerrePositivity.EInfinity.Hammock.PunctureSimplex
public import SerrePositivity.EInfinity.Hammock.RawSurjectionComparison

/-!
# 合成する二列の一方が恒等列である混合縮約

概要：隣接合成と、その二列の一方の恒等列削除の結果は元の語を含めて等しい。
方針：単体圏の面・退化の相殺と、元の包含後の全単体の回収を使う。
規約：どちらの列を削除する場合も扱い、全次数で厳密に同定する。
使われ方：混合 fork の重なる場合の局所合流。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (X Y : C) {n : SimplexCategoryᵒᵖ}

lemma merge_erase_eq_of_cancel {k : ℕ} (d : Fin (k + 2) → Direction)
    (p : Fin (k + 1)) (hp : d p.castSucc = d p.succ) (j : Fin (k + 2))
    (hc : ∀ x, p.predAbove (j.succAbove x) = x)
    (τ : (graph W (⟨k + 2, d⟩ : Word) X Y).obj n)
    (hτ : ∀ r, IdentityColumn (τ.obj r) j) :
    (⟨Word.mergeTarget d p,
      ((graphDiagram W X Y).map (Word.mergeMap d p hp)).app n τ⟩ : RawHammock W X Y n) =
      ⟨Word.erase (⟨k + 2, d⟩ : Word) j, eraseSimplex W X Y j τ hτ⟩ := by
  let σ := punctureSimplex W X Y d j τ hτ
  let e := Word.punctureInclusion d j
  let f := Word.mergeMap d p hp
  have he := raw_eq_of_surjections W X Y (𝟙 (Word.puncture d j)) (e ≫ f)
    Function.surjective_id rfl (fun x => (hc x).symm) n σ
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_comp] at he
  change (⟨Word.puncture d j, σ⟩ : RawHammock W X Y n) =
    ⟨Word.mergeTarget d p, ((graphDiagram W X Y).map f).app n
      (((graphDiagram W X Y).map e).app n σ)⟩ at he
  rw [punctureSimplex_fac] at he
  exact he.symm.trans (punctureSimplex_raw_eq W X Y d j τ hτ)

/-- 合成する二列の一方を削除するなら、二つの縮約の結果は既に同じ。 -/
lemma merge_erase_overlap_eq {k : ℕ} (d : Fin (k + 2) → Direction)
    (p : Fin (k + 1)) (hp : d p.castSucc = d p.succ) (j : Fin (k + 2))
    (hj : j = p.castSucc ∨ j = p.succ)
    (τ : (graph W (⟨k + 2, d⟩ : Word) X Y).obj n)
    (hτ : ∀ r, IdentityColumn (τ.obj r) j) :
    (⟨Word.mergeTarget d p,
      ((graphDiagram W X Y).map (Word.mergeMap d p hp)).app n τ⟩ : RawHammock W X Y n) =
      ⟨Word.erase (⟨k + 2, d⟩ : Word) j, eraseSimplex W X Y j τ hτ⟩ := by
  apply merge_erase_eq_of_cancel W X Y d p hp j ?_ τ hτ
  intro x
  rcases hj with rfl | rfl
  · exact congrArg (fun f : SimplexCategory.mk k ⟶ SimplexCategory.mk k => f.toOrderHom x)
      (SimplexCategory.δ_comp_σ_self (i := p))
  · exact congrArg (fun f : SimplexCategory.mk k ⟶ SimplexCategory.mk k => f.toOrderHom x)
      (SimplexCategory.δ_comp_σ_succ (i := p))

end SerrePositivity.EInfinity.Hammock
