module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SmallPerfectEvaluationKernel

/-!
概要：実評価核の列による厚い生成と完全加群の Morita 同値。
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

def smallPerfectEvaluationKernel_columnComparison (c : HomotopyCategory R (C)) :
    (Morita.kernelDerivedColumn R (C) D
      (ForgetEnrichment.to (Complex R) c.as)).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.smallPerfectEvaluationKernel R D) ≅
      (perfectModuleInclusion R D Set.univ).obj
        ((smallPerfectDGModuleToPerfect R D Set.univ).obj c) :=
  Morita.kernelDerivedColumnComputation R (C) D (ForgetEnrichment.to (Complex R) c.as)
    (BimoduleCategory.of R D (C) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.smallPerfectEvaluationBimodule R D)) ≪≫
      ((moduleToHomotopyDerivedIso R D).app
        (ForgetEnrichment.of (Complex R)
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.smallPerfectEvaluationBimodule R D).obj
            (ForgetEnrichment.to (Complex R) c.as)))).symm

lemma smallPerfectEvaluationKernel_columnsThickGenerate :
    Morita.criterionPerfColumnsThickGenerate R (C) D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.smallPerfectEvaluationKernel R D) := by
  intro P htri hiso hret hcols Y hY
  let : P.IsClosedUnderIsomorphisms := hiso
  obtain ⟨c, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (smallPerfectDGModuleToPerfect R D Set.univ)
    (⟨Y, hY⟩ : PerfectModuleCategoryOver R D Set.univ)
  exact P.prop_of_iso (smallPerfectEvaluationKernel_columnComparison R D c ≪≫
    (perfectModuleInclusion R D Set.univ).mapIso e)
    (hcols (ForgetEnrichment.to (Complex R) c.as))

def smallPerfectEvaluationKernel_perfectEquivalence :
    Morita.CriterionPerfEquivalenceWitness R (C) D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.smallPerfectEvaluationKernel R D) :=
  Morita.criterionPerfEquivalenceOfConditions R (C) D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.smallPerfectEvaluationKernel R D)
    { columnsPerfect := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.smallPerfectEvaluationKernel_columnsPerfect R D
      fullHomQuasiIso := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.smallPerfectEvaluationKernel_fullHomQuasiIso R D
      columnsThickGenerate := smallPerfectEvaluationKernel_columnsThickGenerate R D }

end SerrePositivity.InfinityCategories.Project.DerivedCategories
