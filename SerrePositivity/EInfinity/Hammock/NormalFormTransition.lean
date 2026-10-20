module

public import SerrePositivity.EInfinity.Hammock.WordFactorization
public import SerrePositivity.EInfinity.Hammock.NormalForm
public import SerrePositivity.EInfinity.Hammock.RawEmbeddingComparison
public import SerrePositivity.EInfinity.Hammock.EraseEmbedding

/-!
# 元の全語の全遷移に対する正規形の不変性

概要：任意の色保存単調写像による元の遷移は、元の有限縮約の正規形を保つ。
方針：始域・終域の長さの和で帰納し、合成または一列挿入を分離する。
規約：全単射は元の包含の比較で同定する。余極限内の値の一致は使わない。
使われ方：元の全語の余錐への正規化の降下。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (X Y : C) (n : SimplexCategoryᵒᵖ)

lemma normalForm_transition_bijective {a b : Word} (f : a ⟶ b)
    (hf : Function.Bijective f.orderHom) (τ : (graph W a X Y).obj n) :
    normalForm W X Y n ⟨b, ((graphDiagram W X Y).map f).app n τ⟩ =
      normalForm W X Y n ⟨a, τ⟩ := by
  have he := raw_eq_of_embeddings W X Y f (𝟙 b) hf.1 Function.injective_id
    (by rw [Set.range_eq_univ.mpr hf.2]; exact Set.range_id.symm) n τ
    (((graphDiagram W X Y).map f).app n τ) (by rw [CategoryTheory.Functor.map_id]; rfl)
  exact congrArg (normalForm W X Y n) he.symm

/-- 任意の元の語の遷移は、語を含む元の正規形を厳密に保持する。 -/
lemma normalForm_transition {a b : Word} (f : a ⟶ b) (τ : (graph W a X Y).obj n) :
    normalForm W X Y n ⟨b, ((graphDiagram W X Y).map f).app n τ⟩ =
      normalForm W X Y n ⟨a, τ⟩ := by
  classical
  suffices h : ∀ m (a b : Word) (f : a ⟶ b), a.length + b.length = m →
      ∀ τ : (graph W a X Y).obj n,
        normalForm W X Y n ⟨b, ((graphDiagram W X Y).map f).app n τ⟩ =
          normalForm W X Y n ⟨a, τ⟩ from h _ a b f rfl τ
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro a b f hm τ
    by_cases hf : Function.Injective f.orderHom
    · by_cases hs : Function.Surjective f.orderHom
      · exact normalForm_transition_bijective W X Y n f ⟨hf, hs⟩ τ
      · simp only [Function.Surjective, not_forall, not_exists] at hs
        obtain ⟨j, hj⟩ := hs
        cases b with
        | mk l d =>
          cases l with
          | zero => exact Fin.elim0 j
          | succ k =>
            let e := Word.punctureInclusion d j
            obtain ⟨g, hg⟩ := Word.factorEmbedding e (Word.punctureInclusion_injective d j) f (by
              intro x hx
              rw [Word.punctureInclusion_range]
              intro he
              subst x
              obtain ⟨i, hi⟩ := hx
              exact hj i hi)
            let σ := ((graphDiagram W X Y).map g).app n τ
            have hfac : ((graphDiagram W X Y).map e).app n σ =
                ((graphDiagram W X Y).map f).app n τ := by
              rw [← hg, CategoryTheory.Functor.map_comp]
              rfl
            have hred := erase_reduction_of_embedding W X Y e
              (Word.punctureInclusion_injective d j) j (Word.punctureInclusion_range d j)
              σ _ hfac
            have hi := ih (a.length + k) (by change a.length + (k + 1) = m at hm; omega)
              a (Word.puncture d j) g rfl τ
            exact (normalForm_eq_of_reduction W X Y n hred).trans hi
    · cases a with
      | mk l d =>
        cases l with
        | zero => exact False.elim (hf (by intro i; exact Fin.elim0 i))
        | succ l =>
          have hp : ∃ p : Fin l, f.orderHom p.castSucc = f.orderHom p.succ := by
            simpa only [Fin.orderHom_injective_iff, not_forall, not_not] using hf
          obtain ⟨p, hp⟩ := hp
          cases l with
          | zero => exact Fin.elim0 p
          | succ k =>
            let hc := Word.adjacent_color_of_image_eq d f p hp
            obtain ⟨g, hg⟩ := Word.factorMerge d f p hp
            let σ := ((graphDiagram W X Y).map (Word.mergeMap d p hc)).app n τ
            have hfac : ((graphDiagram W X Y).map f).app n τ =
                ((graphDiagram W X Y).map g).app n σ := by
              rw [← hg, CategoryTheory.Functor.map_comp]
              rfl
            have hi := ih (k + 1 + b.length)
              (by change (k + 2) + b.length = m at hm; omega)
              (Word.mergeTarget d p) b g rfl σ
            rw [hfac]
            exact hi.trans (normalForm_eq_of_reduction W X Y n
              (Reduction.merge d p hc τ)).symm

end SerrePositivity.EInfinity.Hammock
