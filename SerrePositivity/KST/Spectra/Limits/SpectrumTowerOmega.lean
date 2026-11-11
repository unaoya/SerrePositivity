module
public import SerrePositivity.KST.Spectra.PostMappingFibration

public import SerrePositivity.KST.Spectra.Limits.SpectrumTowerSequence

/-!
概要：段ごとに fibration の Ω 条件を持つ Kan 列の塔の極限も Ω 条件を持つ。
方針：全基点 π_* 同型の塔の極限での保存を随伴構造射の厳密比較へ適用する。
規約：構造射の単射性と Sp 内の極限錐は別途検証する。
使われ方：BF 1978 §2、HA §1.4.2、HTT 4.2.4.1、Sp の塔の極限対象。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 概要：Ω 条件を持つ Kan 列の塔の随伴比較射は全基点 π_* 同型。
方針：各段の随伴構造射とその厳密可換性を点つき塔の比較定理へ渡す。
規約：両塔の遷移の fibration 性は元の遷移と loop の fibration 保存から得る。
使われ方：実際の極限の構造射の Ω 条件の検証。 -/
lemma towerSequenceAdjointMap_piIsomorphism (X : ℕ → KanSequence.{u})
    (d : ∀ n, KanSequence.Hom (X (n + 1)) (X n))
    [∀ n k, Fibration ((d n).app k).right]
    (hX : ∀ n, (X n).OmegaCondition) (k : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (towerSequenceAdjointMap X d k).right := by
  change _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.towerMap
    (fun n ↦ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _ ((X n).sigma k)).right)
    (fun n ↦ congrArg Under.Hom.right ((d n).adjoint_comm k)))
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerMap_piIsomorphism
    (fun n ↦ ((X n).level k).space) (fun n ↦ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace ((X n).level (k + 1)).space)
    (fun n ↦ (d n).app k)
    (fun n ↦ PointedObject.basedHomMap PointedSimplicialSet.circle.{u} ((d n).app (k + 1)))
    (fun n ↦ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _ ((X n).sigma k))
    (fun n ↦ (d n).adjoint_comm k) (fun n ↦ hX n k)

/-- 概要：Ω 条件は段ごとの fibration の塔の明示的極限の Kan 列へ保存される。
方針：随伴構造射と loop の極限保存の同型の合成を塔の比較射に同定する。
規約：全基点・全自然数次数を扱い、構造射の単射性は仮定しない。
使われ方：Sp の塔の実際の極限対象の Ω 条件。 -/
lemma towerKanSequence_omega (X : ℕ → KanSequence.{u})
    (d : ∀ n, KanSequence.Hom (X (n + 1)) (X n))
    [∀ n k, Fibration ((d n).app k).right]
    (hX : ∀ n, (X n).OmegaCondition) : (towerKanSequence X d).OmegaCondition := by
  intro k
  have hi : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.loopTowerIso (fun n ↦ ((X n).level (k + 1)).space)
        (fun n ↦ (d n).app (k + 1))).hom.right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanPiIsomorphism.of_iso
      (X := (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerLimit (fun n ↦ ((X n).level (k + 1)).space)
        (fun n ↦ (d n).app (k + 1)))).right)
      (Y := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTowerLimit (fun n ↦ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace ((X n).level (k + 1)).space)
        (fun n ↦ PointedObject.basedHomMap PointedSimplicialSet.circle.{u}
          ((d n).app (k + 1)))).right)
      (PointedSimplicialSet.forget.mapIso
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.loopTowerIso (fun n ↦ ((X n).level (k + 1)).space)
        (fun n ↦ (d n).app (k + 1))))
  have h := towerSequenceAdjointMap_piIsomorphism X d hX k
  have he := congrArg Under.Hom.right (towerSequenceSigma_adjoint X d k)
  simp only [Under.comp_right] at he
  rw [← he] at h
  exact h.of_comp hi

end
end SerrePositivity.InfinityCategories.HomotopyLimits
