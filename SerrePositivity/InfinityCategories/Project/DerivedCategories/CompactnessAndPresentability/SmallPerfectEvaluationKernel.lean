module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.SmallPerfectEvaluationBimodule

/-!
概要：実評価双加群の導来核と列の完全性。
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

def smallPerfectEvaluationKernel : Morita.Kernel R (C) D :=
  (bimoduleToDerived R D (C)).obj
    (BimoduleCategory.of R D (C) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.smallPerfectEvaluationBimodule R D))

lemma smallPerfectEvaluationKernel_columnsPerfect :
    Morita.kernelColumnsPerfect R (C) D (smallPerfectEvaluationKernel R D) := by
  apply (Morita.kernelColumnsPerfect_ofBimodule_iff R (C) D
    (BimoduleCategory.of R D (C) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.smallPerfectEvaluationBimodule R D))).mpr
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.smallPerfectEvaluationBimodule_column_perfect R D

lemma smallPerfectEvaluationKernel_fullHomQuasiIso :
    Morita.criterionPerfKernelFullHomQuasiIso R (C) D (smallPerfectEvaluationKernel R D) :=
  ⟨BimoduleCategory.of R D (C) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.smallPerfectEvaluationBimodule R D), ⟨Iso.refl _⟩,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.smallPerfectEvaluationBimodule_fullHomQuasiIso R D⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
