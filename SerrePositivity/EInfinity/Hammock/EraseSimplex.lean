module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordErasure
public import SerrePositivity.EInfinity.Hammock.ProperDiagram

/-!
# 元の全単体から恒等列を一つ削除する操作

概要：全行が恒等列である一列を削除し、同じ元の全射列の原像を回収する。
方針：完成済みの像の特徴付けと単射性を使う。
規約：削除対象を同型類だけで指定せず、元の包含後の厳密な一致を証明する。
使われ方：縮約 hammock の基本削除と元の余極限への整合。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (X Y : C) {w : Word} (j : Fin w.length) {n : SimplexCategoryᵒᵖ}
  (τ : (graph W w X Y).obj n) (hτ : ∀ k, IdentityColumn (τ.obj k) j)
include hτ

lemma exists_eraseSimplex : ∃ σ : (graph W (Word.erase w j) X Y).obj n,
    ((graphDiagram W X Y).map (Word.eraseInclusion w j)).app n σ = τ :=
  (graphDiagram_map_range_iff_identityOutside (Word.eraseInclusion w j)
    (Word.eraseInclusion_injective w j) n τ).2
      (fun k => (identityOutside_erase_iff (τ.obj k) j).2 (hτ k))

/-- 全行が恒等である元の一列を削除した、同じ全射列の原像。 -/
def eraseSimplex : (graph W (Word.erase w j) X Y).obj n :=
  Classical.choose (exists_eraseSimplex W X Y j τ hτ)

lemma eraseSimplex_fac :
    ((graphDiagram W X Y).map (Word.eraseInclusion w j)).app n
      (eraseSimplex W X Y j τ hτ) = τ :=
  Classical.choose_spec (exists_eraseSimplex W X Y j τ hτ)

lemma eraseSimplex_unique (σ : (graph W (Word.erase w j) X Y).obj n)
    (hσ : ((graphDiagram W X Y).map (Word.eraseInclusion w j)).app n σ = τ) :
    σ = eraseSimplex W X Y j τ hτ := by
  apply graphDiagram_map_app_injective W _ (Word.eraseInclusion_injective w j) X Y n
  exact hσ.trans (eraseSimplex_fac W X Y j τ hτ).symm

end SerrePositivity.EInfinity.Hammock
