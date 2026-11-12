module

public import SerrePositivity.KST.Spectra.StandardEndSequenceComparison
public import SerrePositivity.KST.Spectra.PostMappingIsomorphism

/-!
概要：Reedy 条件を持つ Ω 列の通常 Tot は Ω 列。
方針：BK end の Ω 条件と比較射の全基点 π 同型を使い、loop 比較を合成から消去する。
規約：元の係数の Ω 条件と Reedy 条件だけを仮定する。
使われ方：Goerss–Jardine VIII §1、BF 1978 §2。通常 Tot の BF 単射置換への入力。
-/

@[expose] public section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra.KanSequence
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 通常 Tot の実際の end の列は、係数の Ω 条件を保つ。 -/
lemma ordinaryTotalization_omegaCondition (D : CosimplicialObject KanSequence.{u})
    (hD : TotalizationReedy D) (hΩ : ∀ j, (D.obj j).OmegaCondition) :
    (ordinaryTotalization D hD).OmegaCondition := by
  intro n
  let f := totalizationComparison D hD
  have hf : ∀ k, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (f.app k).right := totalizationComparison_levelwise D hD
  have hY := homotopyLimit_omegaCondition (AsSmall.down ⋙ D)
    (fun j ↦ hΩ (AsSmall.down.obj j))
  have hpost := PointedMapping.post_piIsomorphism PointedSimplicialSet.circle.{u}
    (f.app (n + 1)) (hf (n + 1))
  have h := (hf n).comp (hY n)
  change _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (f.app n ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv
    ((homotopyLimit (AsSmall.down ⋙ D)).level n).space
    ((homotopyLimit (AsSmall.down ⋙ D)).level (n + 1)).space
    ((homotopyLimit (AsSmall.down ⋙ D)).sigma n)).right at h
  rw [f.adjoint_comm n] at h
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp h hpost

end
end SerrePositivity.KST.Spectra.KanSequence
