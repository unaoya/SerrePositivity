module
public import SerrePositivity.KST.NonConnective.DGKappaResolvedEvaluationMorita
public import SerrePositivity.InfinityCategories.Derived.DGPerfectKernelMoritaInfinity
public import SerrePositivity.DifferentialGraded.Perfect.SmallEnhancement

/-!
概要：同じ実評価 Morita 核の主作用を、元の実 ∞-Perf の同値へ接続する。
方針：D の小 Perf 代表系と全主導来対象の局所生成を両側へ適用し、正本の実核比較を使う。
規約：明示 I・P に条件付き。compact 生成を新しい入力仮定にせず、同じ実評価核を保持する。
使われ方：K-7 c5 の実小核の Perf と、元の固定 ν の Perf 値との照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R]

private def evaluationCompactFamily (C : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
    (x : SmallPerfectDGModuleOver R C Set.univ) : DerivedModuleCategory R C :=
  (perfectModuleInclusion R C Set.univ).obj ((smallPerfectDGModuleToPerfect R C Set.univ).obj
    ((toHomotopy R (SmallPerfectDGModuleOver R C Set.univ)).obj (ForgetEnrichment.of (Complex R) x)))

private theorem evaluationCompactGeneration (C : Type (max (u + 1) v))
    [DGCategory R C] [Small.{u} C] :
    Morita.CriterionDerivedCompactGeneration R C (evaluationCompactFamily R C) where
  compact x := (moduleCompact_iff_perfect R C _).mpr
    ((smallPerfectDGModuleToPerfect R C Set.univ).obj
      ((toHomotopy R (SmallPerfectDGModuleOver R C Set.univ)).obj
        (ForgetEnrichment.of (Complex R) x))).property
  localizing Q htri hiso hcop hgen X := by
    letI := htri
    letI := hiso
    have hperf : ∀ Y : DerivedModuleCategory R C, modulePerfect R C Y → Q Y := by
      intro Y hY
      obtain ⟨c, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (smallPerfectDGModuleToPerfect R C Set.univ)
        (⟨Y, hY⟩ : PerfectModuleCategoryOver R C Set.univ)
      exact Q.prop_of_iso ((perfectModuleInclusion R C Set.univ).mapIso e)
        (hgen (ForgetEnrichment.to (Complex R) c.as))
    exact moduleLocalizing_all R C Q hcop hperf X

variable (D : Type (max (u + 1) v)) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ) (P : DGKappaPerfectInput R D I)

include P in
/-- I・P に条件付きで、同じ実評価核の全主導来作用は元の三条件により同値。 -/
theorem dgKappaResolvedEvaluationClassical_isEquivalence :
    (Morita.kernelDerivedTensorOnBimodule R (dgKappaResolvedKernelKInput R D I) D
      (dgKappaResolvedEvaluationBimodule R D I)).IsEquivalence :=
  dgKernelClassical_isEquivalence_of_morita R (dgKappaResolvedKernelKInput R D I) D
    (dgKappaResolvedEvaluationBimodule R D I)
    ⟨dgKappaResolvedEvaluationKernel_columnsPerfect R D I P,
      dgKappaResolvedEvaluationKernel_fullHomQuasiIso R D I,
      dgKappaResolvedEvaluationKernel_columnsThickGenerate R D I P⟩
    (evaluationCompactFamily R (dgKappaResolvedKernelKInput R D I))
    (evaluationCompactGeneration R (dgKappaResolvedKernelKInput R D I))
    (evaluationCompactFamily R D) (evaluationCompactGeneration R D)

/-- I・P に条件付きで、同じ実評価核の元の実 ∞-Perf 作用。 -/
def dgKappaResolvedPerfectInfinity :
    dgModulePerfectInfinityCategory R (dgKappaResolvedKernelKInput R D I) ⟶
      dgModulePerfectInfinityCategory R D := by
  let := dgKappaResolvedEvaluationClassical_isEquivalence R D I P
  exact dgPerfectKernelInfinity R (dgKappaResolvedKernelKInput R D I) D
    (dgKappaResolvedEvaluationBimodule R D I)

/-- I・P に条件付きで、同じ実 ∞-Perf 作用は全写像空間の同値。 -/
theorem dgKappaResolvedPerfectInfinity_isQCatEquivalence :
    IsQCatEquivalence (dgKappaResolvedPerfectInfinity R D I P) := by
  let := dgKappaResolvedEvaluationClassical_isEquivalence R D I P
  exact dgPerfectKernelInfinity_isQCatEquivalence_of_classical R
    (dgKappaResolvedKernelKInput R D I) D (dgKappaResolvedEvaluationBimodule R D I)

/-- I・P に条件付きで、同じ ∞-Perf 作用の包含は元の同じ実導来 kernel 作用と全関手で可換。 -/
def dgKappaResolvedPerfectInfinity_inclusionIso :
    FunctorIso (dgKappaResolvedPerfectInfinity R D I P ≫ dgPerfectInclusionInfinity R D)
      (dgPerfectInclusionInfinity R (dgKappaResolvedKernelKInput R D I) ≫
        dgKernelDerivedInfinity R (dgKappaResolvedKernelKInput R D I) D
          (dgKappaResolvedEvaluationBimodule R D I)) := by
  let := dgKappaResolvedEvaluationClassical_isEquivalence R D I P
  exact dgPerfectKernelInclusionIso R (dgKappaResolvedKernelKInput R D I) D
    (dgKappaResolvedEvaluationBimodule R D I)

end SerrePositivity.KST.NonConnective
