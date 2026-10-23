module

public import SerrePositivity.EInfinity.Hammock.TensorHomotopy
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ContinuousKanProductUnit
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ContinuousKanWeakFunctoriality
public import SerrePositivity.InfinityCategories.F1B.WeakWhitehead

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
    {f : A ⟶ B} {g : C ⟶ D} (hf : IsSimplicialHomotopyEquivalence f)
    (hg : IsSimplicialHomotopyEquivalence g) : IsSimplicialHomotopyEquivalence (f ⊗ₘ g) := by
  obtain ⟨i, ⟨H₀⟩, ⟨H₁⟩⟩ := hf
  obtain ⟨j, ⟨K₀⟩, ⟨K₁⟩⟩ := hg
  refine ⟨i ⊗ₘ j, ?_, ?_⟩
  · rw [tensorHom_comp_tensorHom, ← id_tensorHom_id]
    exact ⟨tensorHomotopy H₀ K₀⟩
  · rw [tensorHom_comp_tensorHom, ← id_tensorHom_id]
    exact ⟨tensorHomotopy H₁ K₁⟩

lemma weakTensor {A B C D : SSet.{u}} {f : A ⟶ B} {g : C ⟶ D}
    (hf : IsWeakHomotopyEquivalence f) (hg : IsWeakHomotopyEquivalence g) :
    IsWeakHomotopyEquivalence (f ⊗ₘ g) := by
  have hfQ := F2.continuousKanReplacement_map_isWeakHomotopyEquivalence f hf
  have hgQ := F2.continuousKanReplacement_map_isWeakHomotopyEquivalence g hg
  have hQ := (tensor_isSimplicialHomotopyEquivalence hfQ.isSimplicialHomotopyEquivalence
    hgQ.isSimplicialHomotopyEquivalence).isWeakHomotopyEquivalence
  have hs := F2.continuousKanProductUnit_isWeakHomotopyEquivalence A C
  have ht := F2.continuousKanProductUnit_isWeakHomotopyEquivalence B D
  have hn : (f ⊗ₘ g) ≫ (F2.continuousKanReplacementUnit.app B ⊗ₘ
      F2.continuousKanReplacementUnit.app D) =
      (F2.continuousKanReplacementUnit.app A ⊗ₘ F2.continuousKanReplacementUnit.app C) ≫
        (F2.continuousKanReplacement.map f ⊗ₘ F2.continuousKanReplacement.map g) := by
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
    exact congrArg₂ (fun a b => a ⊗ₘ b)
      (F2.continuousKanReplacementUnit.naturality f)
      (F2.continuousKanReplacementUnit.naturality g)
  exact ht.cancel_right (hn.symm ▸ hs.comp hQ)

end SerrePositivity.EInfinity.Hammock
