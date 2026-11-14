module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TensorHomotopy
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.ContinuousKanProductUnit
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ContinuousKanWeakFunctoriality
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakWhitehead
public import Mathlib.Tactic.CrossRefAttribute

/-!
# 元の二つの弱ホモトピー同値の直積

概要：元の任意の二つの単体集合の弱比較の直積も弱比較となる。
方針：連続 Kan 置換後の実際のホモトピー逆を直積し、元の単位の直積を消去する。
規約：元の始終域の Kan 性と単体集合モデル構造は要求しない。
使われ方：元の因子列の有限個の指定因子の弱比較。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory MonoidalCategory SerrePositivity.InfinityCategories

lemma tensor_isSimplicialHomotopyEquivalence {A B C D : SSet.{u}}
    {f : A ⟶ B} {g : C ⟶ D} (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence f)
    (hg : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence g) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (f ⊗ₘ g) := by
  obtain ⟨i, ⟨H₀⟩, ⟨H₁⟩⟩ := hf
  obtain ⟨j, ⟨K₀⟩, ⟨K₁⟩⟩ := hg
  refine ⟨i ⊗ₘ j, ?_, ?_⟩
  · rw [tensorHom_comp_tensorHom, ← id_tensorHom_id]
    exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.tensorHomotopy H₀ K₀⟩
  · rw [tensorHom_comp_tensorHom, ← id_tensorHom_id]
    exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.tensorHomotopy H₁ K₁⟩

@[kerodon 02L2]
lemma weakTensor {A B C D : SSet.{u}} {f : A ⟶ B} {g : C ⟶ D}
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence f) (hg : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence g) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (f ⊗ₘ g) := by
  have hfQ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.continuousKanReplacement_map_isWeakHomotopyEquivalence f hf
  have hgQ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.continuousKanReplacement_map_isWeakHomotopyEquivalence g hg
  have hQ := (tensor_isSimplicialHomotopyEquivalence hfQ.isSimplicialHomotopyEquivalence
    hgQ.isSimplicialHomotopyEquivalence).isWeakHomotopyEquivalence
  have hs := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanProductUnit_isWeakHomotopyEquivalence A C
  have ht := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanProductUnit_isWeakHomotopyEquivalence B D
  have hn : (f ⊗ₘ g) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app B ⊗ₘ
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app D) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app A ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app C) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map g) := by
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
    exact congrArg₂ (fun a b => a ⊗ₘ b)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.naturality f)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.naturality g)
  exact ht.cancel_right (hn.symm ▸ hs.comp hQ)

end SerrePositivity.EInfinity.Hammock
