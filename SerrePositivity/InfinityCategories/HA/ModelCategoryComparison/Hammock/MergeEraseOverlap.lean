module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.PunctureSimplex
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawSurjectionComparison

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

namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
open _root_.CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (X Y : C) {n : SimplexCategoryᵒᵖ}

lemma merge_erase_eq_of_cancel {k : ℕ} (d : Fin (k + 2) → _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction)
    (p : Fin (k + 1)) (hp : d p.castSucc = d p.succ) (j : Fin (k + 2))
    (hc : ∀ x, p.predAbove (j.succAbove x) = x)
    (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W (⟨k + 2, d⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) X Y).obj n)
    (hτ : ∀ r, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityColumn (τ.obj r) j) :
    (⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeTarget d p,
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeMap d p hp)).app n τ⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n) =
      ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.erase (⟨k + 2, d⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) j, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.eraseSimplex W X Y j τ hτ⟩ := by
  let σ := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.punctureSimplex W X Y d j τ hτ
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.punctureInclusion d j
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeMap d p hp
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.raw_eq_of_surjections W X Y (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.puncture d j)) (e ≫ f)
    Function.surjective_id rfl (fun x => (hc x).symm) n σ
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_comp] at he
  change (⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.puncture d j, σ⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n) =
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeTarget d p, ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map f).app n
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map e).app n σ)⟩ at he
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.punctureSimplex_fac] at he
  exact he.symm.trans (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.punctureSimplex_raw_eq W X Y d j τ hτ)

/-- 合成する二列の一方を削除するなら、二つの縮約の結果は既に同じ。 -/
lemma merge_erase_overlap_eq {k : ℕ} (d : Fin (k + 2) → _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction)
    (p : Fin (k + 1)) (hp : d p.castSucc = d p.succ) (j : Fin (k + 2))
    (hj : j = p.castSucc ∨ j = p.succ)
    (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W (⟨k + 2, d⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) X Y).obj n)
    (hτ : ∀ r, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityColumn (τ.obj r) j) :
    (⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeTarget d p,
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeMap d p hp)).app n τ⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n) =
      ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.erase (⟨k + 2, d⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) j, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.eraseSimplex W X Y j τ hτ⟩ := by
  apply _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.merge_erase_eq_of_cancel W X Y d p hp j ?_ τ hτ
  intro x
  rcases hj with rfl | rfl
  · exact congrArg (fun f : SimplexCategory.mk k ⟶ SimplexCategory.mk k => f.toOrderHom x)
      (SimplexCategory.δ_comp_σ_self (i := p))
  · exact congrArg (fun f : SimplexCategory.mk k ⟶ SimplexCategory.mk k => f.toOrderHom x)
      (SimplexCategory.δ_comp_σ_succ (i := p))

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
