module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.VertexBoundary
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.ProjectorComponents

/-!
# 正規化作用素の元の頂点列への制限

## 概要
安定正規化作用素は零単体の包含を厳密に固定する。

## 方針
安定性で最初の一段に戻し、零単体での境界の消滅を使う。

## 規約
恒等射へのホモトピーだけでなく、同じ各次数の成分の等式を述べる。

## 使われ方
HA 1.2.4。既存 native 余錐の標準脚の厳密な照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits SSet SerrePositivity.DifferentialGraded
open HomologicalComplex CochainComplex HomComplex
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

/-- 安定正規化の零単体上の制限は、同じ単位の制限に等しい。 -/
theorem dgCoherentBarNormalizationProjectorGraded_restrict_vertex (s : I _⦋0⦌) :
    (eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) ⟨0, s⟩)
      (dgCoherentBarGraded R D F)).f 0 (dgCoherentBarNormalizationProjectorGraded R D F) =
    (eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) ⟨0, s⟩)
      (dgCoherentBarGraded R D F)).f 0
      (unitElement R (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).val := by
  rw [dgCoherentBarNormalizationProjectorGraded_restrict R D F ⟨0, s⟩]
  change (eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) ⟨0, s⟩)
    (dgCoherentBarGraded R D F)).f 0
    (compose R ((unitElement R (ForgetEnrichment.to (Complex R)
      (dgCoherentBarGraded R D F))).val + dgCoherentBarNormalizationBoundaryGraded R D F 0)
      (unitElement R (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).val rfl) = _
  rw [compose_add_left]
  erw [unit_compose, compose_unit]
  rw [map_add, dgCoherentBarNormalizationBoundary_restrict_vertex_zero R D F s, add_zero]

/-- MC 後の正規化自己射も、元の頂点包含の各次数の成分を固定する。 -/
theorem dgCoherentBarNormalizationEndomorphism_vertex_f
    (hMC : dgCoherentBarMaurerCartan R D F) (s : I _⦋0⦌) (x : D) (q : ℤ) :
    ((moduleEvaluation R D x).map (Sigma.ι (dgCoherentBarFamily R D F) ⟨0, s⟩)).f q ≫
      ((moduleEvaluation R D x).map (dgCoherentBarNormalizationEndomorphism R D F hMC)).f q =
      ((moduleEvaluation R D x).map (Sigma.ι (dgCoherentBarFamily R D F) ⟨0, s⟩)).f q := by
  rw [dgCoherentBarNormalizationEndomorphism_evaluation_f]
  have h := congrArg (fun z => ((moduleHomπ R D _ _ x).f 0 z).v q q (add_zero q))
    (dgCoherentBarNormalizationProjectorGraded_restrict_vertex R D F s)
  erw [moduleHomWhiskerRight_apply_π, moduleHomWhiskerRight_apply_π] at h
  simp only [Cochain.comp_v _ _ _ q q q (add_zero q) (add_zero q), Cochain.ofHom_v] at h
  have hu := congrArg (fun z => z.v q q (add_zero q))
    (yoneda_moduleUnit_π R D (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F)) x)
  simp only [Cochain.ofHom_v, HomologicalComplex.id_f] at hu
  change _ = _ ≫ ((moduleHomπ R D
    (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
    (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F)) x).f 0
    (unitElement R (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).val).v q q
      (add_zero q) at h
  rw [hu, Category.comp_id] at h
  exact h

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
