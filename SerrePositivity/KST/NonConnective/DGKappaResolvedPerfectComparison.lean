module
public import SerrePositivity.KST.NonConnective.DGKappaResolvedKernelAugmentation

/-!
概要：P の元の全関手比較を、D-9 の同じ実小核の native nerve へ戻す。
方針：同じ制限増大の全写像空間の同値を逆に通し、元の包含比較を全関手同型で保持する。
規約：P の明示供給に条件付き。実核の Perf 完備化との同値まで証明済みとは扱わない。
使われ方：K-7 c5 の Perf・P 照合。対象対応だけではなく元の導来模型への全包含を残す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.NonConnective

variable (R : Type u) [CommRing R] (D : Type (max (u + 1) v))
  [DGCategory R D] [Small.{u} D] {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 同じ実核同値の逆と元の包含を通る全関手は、元の perfect 安定閉包の包含と同型。 -/
def dgKappaResolvedKernelInverse_inclusionIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((dgKappaResolvedKernelNerveEquivalence R D I).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgKappaResolvedKernelInputMap R D I).down ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (DGCategoryCellResolution.augmentation R (DGKappaCone R D I)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureInclusion R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I)) := by
  have h := (dgKappaResolvedKernelNerveEquivalence R D I).invHomIso.postcomp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureInclusion R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I))
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (((dgKappaResolvedKernelNerveEquivalence R D I).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgKappaResolvedKernelAugmentation R D I)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureInclusion R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I))
    (𝟙 _ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureInclusion R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I)) at h
  rw [Category.id_comp, Category.assoc, dgKappaResolvedKernelAugmentation_nerve_inclusion] at h
  exact h

variable (P : DGKappaPerfectInput R D I)

/-- P に条件付きで、元の実 Perf から同じ分解核の native nerve への全関手。 -/
def dgKappaPerfectResolvedComparison :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModulePerfectInfinityCategory R D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (dgKappaResolvedKernelKInput R D I) :=
  P.comparison ≫ (dgKappaResolvedKernelNerveEquivalence R D I).inv

/-- P に条件付きで、同じ元の実 Perf と実小核の比較は全写像空間の同値。 -/
theorem dgKappaPerfectResolvedComparison_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (dgKappaPerfectResolvedComparison R D I P) :=
  P.isEquivalence.comp (dgKappaResolvedKernelNerveEquivalence R D I).symm.isQCatEquivalence

/-- P に条件付きで、同じ元の実核包含と増大を通る導来模型への全関手比較を保持する。 -/
def dgKappaPerfectResolvedComparison_inclusion :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (((dgKappaPerfectResolvedComparison R D I P ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgKappaResolvedKernelInputMap R D I).down) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (DGCategoryCellResolution.augmentation R (DGKappaCone R D I))) ≫
            dgKappaConeDerivedComparison R D I)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectInclusionInfinity R D) := by
  have h := (dgKappaResolvedKernelInverse_inclusionIso R D I).precomp P.comparison
  have h' := h.postcomp (dgKappaConeDerivedComparison R D I)
  simpa only [dgKappaPerfectResolvedComparison, Category.assoc] using!
    h' ≪≫ P.inclusion

end SerrePositivity.KST.NonConnective
