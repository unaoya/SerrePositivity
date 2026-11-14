module
public import SerrePositivity.DifferentialGraded.Perfect.Compact.Enhancement
public import SerrePositivity.DifferentialGraded.Morita.Adjunction.Construction

/-!
概要：小さい完全 dg 加群圏の実評価双加群。
方針：既存の実評価・導来 tensor と完全加群の厚い閉包を使う。
規約：生成性の結論を追加仮定にしない。使われ方：β5 と K-S• の実自由代表。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
local notation "C" => SmallPerfectDGModuleOver R D Set.univ

def smallPerfectEvaluationBimodule : Bimodule R D (C) :=
  (smallPerfectDGModuleInclusion R D Set.univ).comp (perfectDGModuleInclusion R D Set.univ)

lemma smallPerfectEvaluationBimodule_column_projective (c : C) :
    moduleHomotopicallyProjective R D (ForgetEnrichment.of (Complex R)
      ((smallPerfectEvaluationBimodule R D).rightAt c)) := c.val.property.1

lemma smallPerfectEvaluationBimodule_column_perfect (c : C) :
    modulePerfect R D ((moduleToDerived R D).obj (ForgetEnrichment.of (Complex R)
      ((smallPerfectEvaluationBimodule R D).rightAt c))) := c.val.property.2

lemma smallPerfectEvaluationBimodule_fullHomQuasiIso :
    Morita.criterionPerfFullHomQuasiIso R (C) D (smallPerfectEvaluationBimodule R D) := by
  intro c c'
  rw [Morita.criterionPerfHomComparison_projective_iff R (C) D
    (smallPerfectEvaluationBimodule R D) c c'
      (smallPerfectEvaluationBimodule_column_projective R D c)]
  change QuasiIso ((𝟙 _) ≫ 𝟙 _)
  rw [Category.id_comp]
  infer_instance

end SerrePositivity.InfinityCategories.Project.DerivedCategories
