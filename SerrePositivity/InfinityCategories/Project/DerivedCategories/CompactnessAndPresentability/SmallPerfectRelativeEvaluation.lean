module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.SmallPerfectEvaluationBimodule
public import SerrePositivity.DifferentialGraded.Morita.CriterionPerfTriangulated
/-!
概要：指定生成集合 S の小 Perf 模型の実評価核と、その完全忠実な主 Perf 作用を構成する。
方針：全 Hom 恒等な実評価の射影的列に Morita の Hom 判定を適用する。
規約：全 Perf の対象型の Small 性を要求しない。既存の全生成集合版は保持する。
使われ方：D-18 の tria の代表可能性と小 Perf の前三角性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D] (S : Set D)
local notation "C" => SmallPerfectDGModuleOver R D S

def smallPerfectRelativeEvaluation : Bimodule R D (C) :=
  (smallPerfectDGModuleInclusion R D S).comp (perfectDGModuleInclusion R D S)

def smallPerfectRelativeEvaluationKernel : Morita.Kernel R (C) D :=
  (bimoduleToDerived R D (C)).obj
    (BimoduleCategory.of R D (C) (smallPerfectRelativeEvaluation R D S))

lemma smallPerfectRelativeEvaluation_columnsPerfect :
    Morita.kernelColumnsPerfect R (C) D (smallPerfectRelativeEvaluationKernel R D S) := by
  apply (Morita.kernelColumnsPerfect_ofBimodule_iff R (C) D
    (BimoduleCategory.of R D (C) (smallPerfectRelativeEvaluation R D S))).mpr
  intro c
  exact modulePerfectOver_mono R D (Set.subset_univ S) _ c.val.property.2

lemma smallPerfectRelativeEvaluation_fullHomQuasiIso :
    Morita.criterionPerfKernelFullHomQuasiIso R (C) D
      (smallPerfectRelativeEvaluationKernel R D S) := by
  refine ⟨BimoduleCategory.of R D (C) (smallPerfectRelativeEvaluation R D S),
    ⟨Iso.refl _⟩, ?_⟩
  change Morita.criterionPerfFullHomQuasiIso R (C) D
    (smallPerfectRelativeEvaluation R D S)
  intro c c'
  rw [Morita.criterionPerfHomComparison_projective_iff R (C) D
    (smallPerfectRelativeEvaluation R D S) c c' c.val.property.1]
  change QuasiIso ((𝟙 _) ≫ 𝟙 _)
  rw [Category.id_comp]
  infer_instance

def smallPerfectRelativeEvaluation_perfectFullyFaithful :
    (Morita.perfectDerivedKernelAction R (C) D (smallPerfectRelativeEvaluationKernel R D S)
      (smallPerfectRelativeEvaluation_columnsPerfect R D S)).FullyFaithful :=
  Morita.criterionPerfFullyFaithfulOfRepresentables R (C) D _
    (smallPerfectRelativeEvaluation_columnsPerfect R D S)
    ((Morita.criterionPerfKernelFullHomQuasiIso_iff_representableMaps R (C) D _).mp
      (smallPerfectRelativeEvaluation_fullHomQuasiIso R D S))

def smallPerfectRelativeEvaluation_representableIso (c : C) :
    (Morita.kernelDerivedTensor R (C) D (smallPerfectRelativeEvaluationKernel R D S)).obj
      (Morita.criterionPerfRepresentable R (C) c) ≅
      (moduleToDerived R D).obj (ForgetEnrichment.of (Complex R) c.val.val) :=
  Morita.kernelDerivedColumnActionIso R (C) D _ c ≪≫
    Morita.kernelDerivedColumnComputation R (C) D c
      (BimoduleCategory.of R D (C) (smallPerfectRelativeEvaluation R D S))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
