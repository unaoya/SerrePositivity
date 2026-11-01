module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordPuncture
public import SerrePositivity.EInfinity.Hammock.EraseEmbedding

/-!
# 明示的な一列削除による元の全単体の回収

概要：Fin.succAbove の包含で元の恒等列を削除し、既存の削除と厳密に同定する。
方針：一列の補集合を像とする包含の回収を使う。
規約：元の全次数の単体と語を保持し、元の包含後の一致も証明する。
使われ方：合成と削除の混合 fork。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (X Y : C) {k : ℕ} (d : Fin (k + 1) → Direction) (j : Fin (k + 1))
  {n : SimplexCategoryᵒᵖ} (τ : (graph W (⟨k + 1, d⟩ : Word) X Y).obj n)
  (hτ : ∀ r, IdentityColumn (τ.obj r) j)
include hτ

def punctureSimplex : (graph W (Word.puncture d j) X Y).obj n :=
  Classical.choose (exists_eraseEmbedding W X Y (Word.punctureInclusion d j)
    (Word.punctureInclusion_injective d j) j (Word.punctureInclusion_range d j) τ hτ)

lemma punctureSimplex_fac :
    ((graphDiagram W X Y).map (Word.punctureInclusion d j)).app n
      (punctureSimplex W X Y d j τ hτ) = τ :=
  (Classical.choose_spec (exists_eraseEmbedding W X Y (Word.punctureInclusion d j)
    (Word.punctureInclusion_injective d j) j (Word.punctureInclusion_range d j) τ hτ)).1

lemma punctureSimplex_raw_eq :
    (⟨Word.puncture d j, punctureSimplex W X Y d j τ hτ⟩ : RawHammock W X Y n) =
      ⟨Word.erase (⟨k + 1, d⟩ : Word) j, eraseSimplex W X Y j τ hτ⟩ :=
  (Classical.choose_spec (exists_eraseEmbedding W X Y (Word.punctureInclusion d j)
    (Word.punctureInclusion_injective d j) j (Word.punctureInclusion_range d j) τ hτ)).2

end SerrePositivity.EInfinity.Hammock
