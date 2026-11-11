module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordPuncture
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
  (X Y : C) {k : ℕ} (d : Fin (k + 1) → _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (j : Fin (k + 1))
  {n : SimplexCategoryᵒᵖ} (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W (⟨k + 1, d⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) X Y).obj n)
  (hτ : ∀ r, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityColumn (τ.obj r) j)
include hτ

def punctureSimplex : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.puncture d j) X Y).obj n :=
  Classical.choose (exists_eraseEmbedding W X Y (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.punctureInclusion d j)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.punctureInclusion_injective d j) j (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.punctureInclusion_range d j) τ hτ)

lemma punctureSimplex_fac :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.punctureInclusion d j)).app n
      (punctureSimplex W X Y d j τ hτ) = τ :=
  (Classical.choose_spec (exists_eraseEmbedding W X Y (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.punctureInclusion d j)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.punctureInclusion_injective d j) j (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.punctureInclusion_range d j) τ hτ)).1

lemma punctureSimplex_raw_eq :
    (⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.puncture d j, punctureSimplex W X Y d j τ hτ⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n) =
      ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.erase (⟨k + 1, d⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) j, eraseSimplex W X Y j τ hτ⟩ :=
  (Classical.choose_spec (exists_eraseEmbedding W X Y (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.punctureInclusion d j)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.punctureInclusion_injective d j) j (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.punctureInclusion_range d j) τ hτ)).2

end SerrePositivity.EInfinity.Hammock
