module
public import SerrePositivity.KST.NonConnective.DGKappaResolvedEvaluationPerfect

/-!
概要：同じ D-9 実小核の実評価双加群について、D 正本の Perf Morita 三条件を検証する。
方針：P による全 perfect 加群の回収を列の厚い生成へ送り、実 Hom 比較と合わせる。
規約：明示 I・P に条件付き。一般の Morita 判定・導来列比較を K-B 内に重ねない。
使われ方：K-7 c5 の同じ実核の Perf と、元の Perf・P との照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type (max (u + 1) v))
  [DGCategory R D] [Small.{u} D] {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 同じ実評価双加群の、元の D 正本の導来核。 -/
def dgKappaResolvedEvaluationKernel : Morita.Kernel R (dgKappaResolvedKernelKInput R D I) D :=
  (bimoduleToDerived R D (dgKappaResolvedKernelKInput R D I)).obj
    (BimoduleCategory.of R D (dgKappaResolvedKernelKInput R D I)
      (dgKappaResolvedEvaluationBimodule R D I))

/-- 同じ導来核の列は、元の同じ実評価加群の主導来像。 -/
def dgKappaResolvedEvaluationKernel_columnComparison (x : dgKappaResolvedKernelKInput R D I) :
    (Morita.kernelDerivedColumn R (dgKappaResolvedKernelKInput R D I) D x).obj
      (dgKappaResolvedEvaluationKernel R D I) ≅
    (moduleToDerived R D).obj (ForgetEnrichment.of (Complex R)
      ((dgKappaResolvedEvaluationBimodule R D I).rightAt x)) :=
  Morita.kernelDerivedColumnComputation R (dgKappaResolvedKernelKInput R D I) D x
    (BimoduleCategory.of R D (dgKappaResolvedKernelKInput R D I)
      (dgKappaResolvedEvaluationBimodule R D I))

/-- I・P に条件付きで、同じ導来評価核の全列は perfect。 -/
theorem dgKappaResolvedEvaluationKernel_columnsPerfect (P : DGKappaPerfectInput R D I) :
    Morita.kernelColumnsPerfect R (dgKappaResolvedKernelKInput R D I) D
      (dgKappaResolvedEvaluationKernel R D I) := by
  intro x
  exact (modulePerfect R D).prop_of_iso
    (dgKappaResolvedEvaluationKernel_columnComparison R D I x).symm
    (dgKappaResolvedEvaluationBimodule_column_perfect R D I P x)

/-- 同じ導来評価核の全 Hom 比較は、検証済みの元の評価双加群の比較。 -/
theorem dgKappaResolvedEvaluationKernel_fullHomQuasiIso :
    Morita.criterionPerfKernelFullHomQuasiIso R (dgKappaResolvedKernelKInput R D I) D
      (dgKappaResolvedEvaluationKernel R D I) :=
  ⟨BimoduleCategory.of R D (dgKappaResolvedKernelKInput R D I)
    (dgKappaResolvedEvaluationBimodule R D I), ⟨Iso.refl _⟩,
      dgKappaResolvedEvaluationBimodule_fullHomQuasiIso R D I⟩

/-- I・P に条件付きで、同じ実評価核の列は元の全 perfect 加群を厚く生成する。 -/
theorem dgKappaResolvedEvaluationKernel_columnsThickGenerate (P : DGKappaPerfectInput R D I) :
    Morita.criterionPerfColumnsThickGenerate R (dgKappaResolvedKernelKInput R D I) D
      (dgKappaResolvedEvaluationKernel R D I) := by
  intro Q _htri hiso _hret hcols Y hY
  let : Q.IsClosedUnderIsomorphisms := hiso
  obtain ⟨c, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (perfectDGModuleToPerfect R D Set.univ)
    (⟨Y, hY⟩ : PerfectModuleCategoryOver R D Set.univ)
  let N : PerfectDGModule R D := ForgetEnrichment.to (Complex R) c.as
  obtain ⟨x, ⟨h⟩⟩ := dgKappaResolvedEvaluationBimodule_covers R D I P N
  exact Q.prop_of_iso (dgKappaResolvedEvaluationKernel_columnComparison R D I x ≪≫ h ≪≫
    ((moduleToHomotopyDerivedIso R D).app
      (ForgetEnrichment.of (Complex R) N.val)).symm ≪≫
    (perfectModuleInclusion R D Set.univ).mapIso e) (hcols x)

/-- I・P に条件付きで、同じ実評価核の元の主導来作用に一致する Perf 同値。 -/
def dgKappaResolvedEvaluationKernel_perfectEquivalence (P : DGKappaPerfectInput R D I) :
    Morita.CriterionPerfEquivalenceWitness R (dgKappaResolvedKernelKInput R D I) D
      (dgKappaResolvedEvaluationKernel R D I) :=
  Morita.criterionPerfEquivalenceOfConditions R (dgKappaResolvedKernelKInput R D I) D
    (dgKappaResolvedEvaluationKernel R D I)
    { columnsPerfect := dgKappaResolvedEvaluationKernel_columnsPerfect R D I P
      fullHomQuasiIso := dgKappaResolvedEvaluationKernel_fullHomQuasiIso R D I
      columnsThickGenerate := dgKappaResolvedEvaluationKernel_columnsThickGenerate R D I P }

end SerrePositivity.KST.NonConnective
