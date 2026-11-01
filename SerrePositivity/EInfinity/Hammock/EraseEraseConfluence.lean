module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordEraseCompositeRange
public import SerrePositivity.EInfinity.Hammock.RawEmbeddingComparison
public import SerrePositivity.EInfinity.Hammock.EraseSimplexIdentityColumn
public import SerrePositivity.EInfinity.Hammock.Reduction

/-!
# 元の二つの恒等列削除の局所合流

概要：二つの基本削除のどちらを先にしても、各側0〜1段で同じ元の対象へ到達する。
方針：残る恒等列を削除し、元の列の像と全射列の回収で二つの結果を同定する。
規約：元の語を含む未縮約対象の等式で、余極限内の値の一致では代用しない。
使われ方：基本縮約全体の局所合流と縮約済みの代表の一意性。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (X Y : C) {w : Word} {n : SimplexCategoryᵒᵖ}

lemma doubleErase_image (j : Fin w.length) (τ : (graph W w X Y).obj n)
    (hj : ∀ k, IdentityColumn (τ.obj k) j) (i : Fin (Word.erase w j).length)
    (hi : ∀ k, IdentityColumn ((eraseSimplex W X Y j τ hj).obj k) i) :
    ((graphDiagram W X Y).map
      ((Word.eraseInclusion (Word.erase w j) i) ≫ Word.eraseInclusion w j)).app n
        (eraseSimplex W X Y i (eraseSimplex W X Y j τ hj) hi) = τ := by
  rw [CategoryTheory.Functor.map_comp]
  change ((graphDiagram W X Y).map (Word.eraseInclusion w j)).app n
    (((graphDiagram W X Y).map (Word.eraseInclusion (Word.erase w j) i)).app n
      (eraseSimplex W X Y i (eraseSimplex W X Y j τ hj) hi)) = τ
  rw [eraseSimplex_fac, eraseSimplex_fac]

/-- 元の二つの基本削除は、各側0〜1段で元の同じ全射列へ合流する。 -/
lemma erase_erase_join (τ : (graph W w X Y).obj n) (j k : Fin w.length)
    (hj : ∀ r, IdentityColumn (τ.obj r) j) (hk : ∀ r, IdentityColumn (τ.obj r) k) :
    ∃ q : RawHammock W X Y n,
      Relation.ReflGen (Reduction W X Y n) ⟨Word.erase w j, eraseSimplex W X Y j τ hj⟩ q ∧
      Relation.ReflGen (Reduction W X Y n) ⟨Word.erase w k, eraseSimplex W X Y k τ hk⟩ q := by
  classical
  by_cases hjk : j = k
  · subst k
    exact ⟨_, Relation.ReflGen.refl, Relation.ReflGen.refl⟩
  have hki : k ∈ Set.range (Word.eraseInclusion w j).orderHom := by
    rw [Word.eraseInclusion_range]
    exact fun h => hjk h.symm
  have hji : j ∈ Set.range (Word.eraseInclusion w k).orderHom := by
    rw [Word.eraseInclusion_range]
    exact hjk
  obtain ⟨i, hi⟩ := hki
  obtain ⟨l, hl⟩ := hji
  let σ := eraseSimplex W X Y j τ hj
  let ρ := eraseSimplex W X Y k τ hk
  have hσ : ∀ r, IdentityColumn (σ.obj r) i :=
    eraseSimplex_identityColumn W X Y j τ hj i (by intro r; rw [hi]; exact hk r)
  have hρ : ∀ r, IdentityColumn (ρ.obj r) l :=
    eraseSimplex_identityColumn W X Y k τ hk l (by intro r; rw [hl]; exact hj r)
  let f := (Word.eraseInclusion (Word.erase w j) i) ≫ Word.eraseInclusion w j
  let g := (Word.eraseInclusion (Word.erase w k) l) ≫ Word.eraseInclusion w k
  have hf : Function.Injective f.orderHom :=
    (Word.eraseInclusion_injective w j).comp (Word.eraseInclusion_injective _ i)
  have hg : Function.Injective g.orderHom :=
    (Word.eraseInclusion_injective w k).comp (Word.eraseInclusion_injective _ l)
  have hfg : Set.range f.orderHom = Set.range g.orderHom := by
    dsimp only [f, g]
    rw [Word.erase_composite_range _ (Word.eraseInclusion_injective w j),
      Word.erase_composite_range _ (Word.eraseInclusion_injective w k),
      hi, hl, Word.eraseInclusion_range, Word.eraseInclusion_range]
    ext a
    simp only [Set.mem_sdiff, Set.mem_compl_iff, Set.mem_singleton_iff, and_comm]
  let q : RawHammock W X Y n := ⟨_, eraseSimplex W X Y i σ hσ⟩
  let q' : RawHammock W X Y n := ⟨_, eraseSimplex W X Y l ρ hρ⟩
  have hq : q = q' := raw_eq_of_embeddings W X Y f g hf hg hfg n q.2 q'.2
    ((doubleErase_image W X Y j τ hj i hσ).trans (doubleErase_image W X Y k τ hk l hρ).symm)
  refine ⟨q, Relation.ReflGen.single (Reduction.erase i σ hσ), ?_⟩
  have hstep : Reduction W X Y n ⟨Word.erase w k, ρ⟩ q := by
    rw [hq]
    exact Reduction.erase l ρ hρ
  exact Relation.ReflGen.single hstep

end SerrePositivity.EInfinity.Hammock
