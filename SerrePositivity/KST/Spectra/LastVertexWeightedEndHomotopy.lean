module

public import SerrePositivity.KST.Spectra.WeightedPreHomotopy
public import SerrePositivity.KST.Spectra.LastVertexWeightHomotopy

/-!
概要：置換した終頂点の重みの射は weighted end への前合成で実際のホモトピー同値を与える。
方針：構成済みの図式ホモトピー逆を AsSmall 上へ制限し、end の前合成へ送る。
規約：係数の Kan 性をこのホモトピー同値の構成に要求しない。
使われ方：Goerss–Jardine VII §4。通常 Tot 比較の置換後の重みの比較。
-/

@[expose] public section
universe u
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.CosimplicialLastVertex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 元の余単体圏の自然な cylinder を AsSmall 上へ制限する。 -/
def smallCylinder {F G : CosimplicialObject SSet.{u}}
    (C : WeightTensorLatching.diagram F (Δ[1] : SSet.{u}) ⟶ G) :
    (AsSmall.down ⋙ F) ⊗ (Functor.const _).obj (Δ[1] : SSet.{u}) ⟶ AsSmall.down ⋙ G where
  app i := C.app (AsSmall.down.obj i)
  naturality _i _j f := C.naturality (AsSmall.down.map f)

/-- 置換後の終頂点射への前合成は全係数で実際の単体的ホモトピー同値。 -/
lemma kanWeightPre_homotopyEquivalence (X : AsSmall.{u} SimplexCategory ⥤ SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre (Functor.whiskerLeft AsSmall.down kanWeightMap.{u}) X) := by
  obtain ⟨H, h₀, h₁, K, k₀, k₁⟩ := kanWeightMap_homotopyInverse.{u}
  let θ := Functor.whiskerLeft AsSmall.down kanWeightMap.{u}
  let η := Functor.whiskerLeft AsSmall.down kanWeightInverse.{u}
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre η X, ?_, ?_⟩
  · have h : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre (η ≫ θ) X)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre (𝟙 _) X) :=
      WeightedPreHomotopy.homotopy (θ := η ≫ θ) (η := 𝟙 _) (smallCylinder K)
        (fun i ↦ k₀ (AsSmall.down.obj i)) (fun i ↦ k₁ (AsSmall.down.obj i)) X
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre_id] at h
    exact ⟨h⟩
  · have h : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre (θ ≫ η) X)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre (𝟙 _) X) :=
      WeightedPreHomotopy.homotopy (θ := θ ≫ η) (η := 𝟙 _) (smallCylinder H)
        (fun i ↦ h₀ (AsSmall.down.obj i)) (fun i ↦ h₁ (AsSmall.down.obj i)) X
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre_id] at h
    exact ⟨h⟩

end
end SerrePositivity.KST.Spectra.CosimplicialLastVertex
