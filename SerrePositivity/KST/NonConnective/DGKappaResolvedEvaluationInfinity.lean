module
public import SerrePositivity.KST.NonConnective.DGKappaResolvedEvaluationMorita
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGPerfectKernelMoritaInfinity
public import SerrePositivity.KST.NonConnective.DGKInputDerivedCompactGeneration

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


variable (D : Type (max (u + 1) v)) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ) (P : DGKappaPerfectInput R D I)

include P in
/-- I・P に条件付きで、同じ実評価核の全主導来作用は元の三条件により同値。 -/
theorem dgKappaResolvedEvaluationClassical_isEquivalence :
    (Morita.kernelDerivedTensorOnBimodule R (dgKappaResolvedKernelKInput R D I) D
      (dgKappaResolvedEvaluationBimodule R D I)).IsEquivalence :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelClassical_isEquivalence_of_morita R (dgKappaResolvedKernelKInput R D I) D
    (dgKappaResolvedEvaluationBimodule R D I)
    ⟨dgKappaResolvedEvaluationKernel_columnsPerfect R D I P,
      dgKappaResolvedEvaluationKernel_fullHomQuasiIso R D I,
      dgKappaResolvedEvaluationKernel_columnsThickGenerate R D I P⟩
    (dgKInputDerivedCompactFamily R (dgKappaResolvedKernelKInput R D I))
    (dgKInputDerivedCompactGeneration R (dgKappaResolvedKernelKInput R D I))
    (dgKInputDerivedCompactFamily R D) (dgKInputDerivedCompactGeneration R D)

/-- I・P に条件付きで、同じ実評価核の元の実 ∞-Perf 作用。 -/
def dgKappaResolvedPerfectInfinity :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModulePerfectInfinityCategory R (dgKappaResolvedKernelKInput R D I) ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModulePerfectInfinityCategory R D := by
  let := dgKappaResolvedEvaluationClassical_isEquivalence R D I P
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectKernelInfinity R (dgKappaResolvedKernelKInput R D I) D
    (dgKappaResolvedEvaluationBimodule R D I)

/-- I・P に条件付きで、同じ実 ∞-Perf 作用は全写像空間の同値。 -/
theorem dgKappaResolvedPerfectInfinity_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (dgKappaResolvedPerfectInfinity R D I P) := by
  let := dgKappaResolvedEvaluationClassical_isEquivalence R D I P
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectKernelInfinity_isQCatEquivalence_of_classical R
    (dgKappaResolvedKernelKInput R D I) D (dgKappaResolvedEvaluationBimodule R D I)

/-- I・P に条件付きで、同じ ∞-Perf 作用の包含は元の同じ実導来 kernel 作用と全関手で可換。 -/
def dgKappaResolvedPerfectInfinity_inclusionIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgKappaResolvedPerfectInfinity R D I P ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectInclusionInfinity R D)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectInclusionInfinity R (dgKappaResolvedKernelKInput R D I) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R (dgKappaResolvedKernelKInput R D I) D
          (dgKappaResolvedEvaluationBimodule R D I)) := by
  let := dgKappaResolvedEvaluationClassical_isEquivalence R D I P
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectKernelInclusionIso R (dgKappaResolvedKernelKInput R D I) D
    (dgKappaResolvedEvaluationBimodule R D I)

end SerrePositivity.KST.NonConnective
