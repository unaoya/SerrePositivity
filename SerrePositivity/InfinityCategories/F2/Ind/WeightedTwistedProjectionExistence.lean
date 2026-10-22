module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedTwistedProjectionRecovery

/-!
概要：同じ底で整合する twisted arrow と weighted 単体から、元の引き戻しの全係数を回収。
方針：同じ初区間の引き戻しを組み、元の二つの射影の値を厳密に検査する。
規約：充填性を仮定しない。使われ方：weighted 全空間の引き戻し性の存在部分。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} {I : Type u} [SmallCategory I]
  (F : I ⥤ RightFibrationObject C)

/-- 元の底で整合する二つの指定単体は、元の weighted 全空間の同じ単体へ持ち上がる。 -/
lemma weightedTwistedProjections_exists {n : ℕ} (t : (edgewiseSubdivision C) _⦋n⦌)
    (s : weightedNerveSimplex (rightFibrationTotalDiagram F) n)
    (h : (edgewiseRight C).app _ t =
      (weightedNerveParameter (rightFibrationProjectionCocone F).ι).app (Opposite.op ⦋n⦌) s) :
    ∃ x : (weightedNerve (strictRightTwistedElementsDiagram F)) _⦋n⦌,
      (weightedTwistedBaseProjection F).app _ x = t ∧
      (weightedTwistedTotalProjection F).app _ x = s := by
  let u := (SSet.yonedaEquiv (X := edgewiseSubdivision C)).symm t
  have hu : u ≫ edgewiseRight C =
      s.2.app (Fin.last n) ≫ (F.obj (s.1.obj (Fin.last n))).val.hom := by
    rw [SSet.yonedaEquiv_symm_comp]
    calc
      _ = SSet.yonedaEquiv.symm
          ((weightedNerveParameter (rightFibrationProjectionCocone F).ι).app (Opposite.op ⦋n⦌) s) :=
        congrArg SSet.yonedaEquiv.symm h
      _ = _ := SSet.yonedaEquiv.symm_apply_apply _
  let φ := weightedTwistedPullbackCoefficient F s u hu
  refine ⟨⟨s.1, φ⟩, ?_, ?_⟩
  · change SSet.yonedaEquiv (φ.app (Fin.last n) ≫ pullback.fst _ _) = t
    dsimp only [φ, weightedTwistedPullbackCoefficient]
    rw [pullback.lift_fst]
    change SSet.yonedaEquiv
      (SSet.stdSimplex.map (simplexPrefixInclusion n n _) ≫ u) = t
    have hi : SSet.stdSimplex.map (simplexPrefixInclusion n n (Nat.le_refl n)) =
        𝟙 (Δ[n] : SSet.{u}) := by
      rw [simplexPrefixInclusion_id, CategoryTheory.Functor.map_id]
    rw [hi, Category.id_comp]
    exact SSet.yonedaEquiv.apply_symm_apply t
  · change (⟨s.1, φ ≫ Functor.whiskerLeft s.1 (strictRightTwistedTotalProjection F)⟩ :
      weightedNerveSimplex (rightFibrationTotalDiagram F) n) = s
    have he : φ ≫ Functor.whiskerLeft s.1 (strictRightTwistedTotalProjection F) = s.2 := by
      apply NatTrans.ext
      funext i
      exact pullback.lift_snd _ _ _
    exact (congrArg (fun q ↦ (⟨s.1, q⟩ :
      weightedNerveSimplex (rightFibrationTotalDiagram F) n)) he).trans (Sigma.eta s)

end SerrePositivity.InfinityCategories.F2.Ind
