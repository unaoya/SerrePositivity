module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ProperDiagram
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordIntersectionFactors
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LengthStage

/-!
# proper 図式の元の二つの包含の原像の重なり

概要：同じ単体を与える二つの包含の原像は、元の交わりから同時に回収できる。
方針：proper の像の交わりと各次数の単射性を使う。
規約：長さ制限段階での原像の一致も元の標準射で照合する。
使われ方：境界の像の和から前の長さ段階への射の構成。
-/

@[expose] public section
universe w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
open _root_.CategoryTheory

variable {F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ SSet.{w}} (hF : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ProperDiagram F)
  {a b c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ c) (g : b ⟶ c)
  (hf : Function.Injective f.orderHom) (hg : Function.Injective g.orderHom)

include hF hf

lemma _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ProperDiagram.map_app_injective (n : SimplexCategoryᵒᵖ) :
    Function.Injective ((F.map f).app n) := by
  have := hF.map_mono f hf
  exact CategoryTheory.injective_of_mono _

include hg

lemma _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ProperDiagram.overlap_lift (n : SimplexCategoryᵒᵖ)
    (σ : (F.obj a).obj n) (τ : (F.obj b).obj n)
    (hστ : (F.map f).app n σ = (F.map g).app n τ) :
    ∃ ρ : (F.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersection f g)).obj n,
      (F.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersectionLeft f g hf)).app n ρ = σ ∧
      (F.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersectionRight f g hg)).app n ρ = τ := by
  have hm : (F.map f).app n σ ∈
      (Subfunctor.range (F.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersectionInclusion f g))).obj n := by
    rw [hF.intersection_range f g hf hg]
    exact ⟨⟨σ, rfl⟩, ⟨τ, hστ.symm⟩⟩
  obtain ⟨ρ, hρ⟩ := hm
  refine ⟨ρ, ?_, ?_⟩
  · apply hF.map_app_injective f hf n
    have he := congrArg (fun h => (F.map h).app n ρ) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersectionLeft_fac f g hf)
    rw [CategoryTheory.Functor.map_comp] at he
    exact he.trans hρ
  · apply hF.map_app_injective g hg n
    have he := congrArg (fun h => (F.map h).app n ρ) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersectionRight_fac f g hg)
    rw [CategoryTheory.Functor.map_comp] at he
    exact he.trans (hρ.trans hστ)

lemma _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ProperDiagram.overlap_lengthStage (n : ℕ) (ha : a.length ≤ n) (hb : b.length ≤ n)
    (k : SimplexCategoryᵒᵖ) (σ : (F.obj a).obj k) (τ : (F.obj b).obj k)
    (hστ : (F.map f).app k σ = (F.map g).app k τ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion F n a ha).app k σ = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion F n b hb).app k τ := by
  obtain ⟨ρ, hσ, hτ⟩ := hF.overlap_lift f g hf hg k σ τ hστ
  have hi := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersection_length_le_left f g hf).trans ha
  have hl := congrArg (fun h => h.app k ρ)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion_naturality F n hi ha (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersectionLeft f g hf))
  have hr := congrArg (fun h => h.app k ρ)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion_naturality F n hi hb (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersectionRight f g hg))
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion F n a ha).app k
    ((F.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersectionLeft f g hf)).app k ρ) = _ at hl
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion F n b hb).app k
    ((F.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersectionRight f g hg)).app k ρ) = _ at hr
  rw [hσ] at hl
  rw [hτ] at hr
  exact hl.trans hr.symm

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
