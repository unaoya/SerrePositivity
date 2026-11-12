module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.WeightedTwistedProjectionRecovery

/-!
概要：同じ底で整合する twisted arrow と weighted 単体から、元の引き戻しの全係数を回収。
方針：同じ初区間の引き戻しを組み、元の二つの射影の値を厳密に検査する。
規約：充填性を仮定しない。使われ方：weighted 全空間の引き戻し性の存在部分。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {C : SSet.{u}} {I : Type u} [SmallCategory I]
  (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject C)

/-- 元の底で整合する二つの指定単体は、元の weighted 全空間の同じ単体へ持ち上がる。 -/
lemma weightedTwistedProjections_exists {n : ℕ} (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision C) _⦋n⦌)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationTotalDiagram F) n)
    (h : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight C).app _ t =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedNerveParameter (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationProjectionCocone F).ι).app (Opposite.op ⦋n⦌) s) :
    ∃ x : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictRightTwistedElementsDiagram F)) _⦋n⦌,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedTwistedBaseProjection F).app _ x = t ∧
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedTwistedTotalProjection F).app _ x = s := by
  let u := (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision C)).symm t
  have hu : u ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight C =
      s.2.app (Fin.last n) ≫ (F.obj (s.1.obj (Fin.last n))).val.hom := by
    rw [SSet.yonedaEquiv_symm_comp]
    calc
      _ = SSet.yonedaEquiv.symm
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedNerveParameter (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationProjectionCocone F).ι).app (Opposite.op ⦋n⦌) s) :=
        congrArg SSet.yonedaEquiv.symm h
      _ = _ := SSet.yonedaEquiv.symm_apply_apply _
  let φ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedTwistedPullbackCoefficient F s u hu
  refine ⟨⟨s.1, φ⟩, ?_, ?_⟩
  · change SSet.yonedaEquiv (φ.app (Fin.last n) ≫ pullback.fst _ _) = t
    dsimp only [φ, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedTwistedPullbackCoefficient]
    rw [pullback.lift_fst]
    change SSet.yonedaEquiv
      (SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion n n _) ≫ u) = t
    have hi : SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion n n (Nat.le_refl n)) =
        𝟙 (Δ[n] : SSet.{u}) := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion_id, CategoryTheory.Functor.map_id]
    rw [hi, Category.id_comp]
    exact SSet.yonedaEquiv.apply_symm_apply t
  · change (⟨s.1, φ ≫ Functor.whiskerLeft s.1 (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictRightTwistedTotalProjection F)⟩ :
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationTotalDiagram F) n) = s
    have he : φ ≫ Functor.whiskerLeft s.1 (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictRightTwistedTotalProjection F) = s.2 := by
      apply NatTrans.ext
      funext i
      exact pullback.lift_snd _ _ _
    exact (congrArg (fun q ↦ (⟨s.1, q⟩ :
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationTotalDiagram F) n)) he).trans (Sigma.eta s)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
