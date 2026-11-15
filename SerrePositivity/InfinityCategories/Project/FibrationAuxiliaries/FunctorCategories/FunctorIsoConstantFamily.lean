module
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluation
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoVertexEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConstantFunctor
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ConstantAdjunct
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerHom

/-!
概要：元の関手同型の定値の全族を同じ頂点成分の像へ正規化する。
方針：既存の同じ図式・射・指定同型の合成則を使う。
規約：元の全パラメータと指定された値を保持する。
使われ方：IS-W2 R03h・R03d の native Hom と同じ roof の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 定値入力への制限を元の合成同型で正規化すると、同じ頂点成分の定値族になる。 -/
lemma sameFunctorIso_constant_family {K X : SSet.{u}} [Quasicategory K] [Quasicategory X]
    (T : SSet.{u}) {f g : K ⟶ X} (e : FunctorIso f g) (x : K _⦋0⦌) :
    (constantFunctorCompIso T x f).inv ≫
      (e.precomp (SSet.const x : T ⟶ K)).hom ≫
      (constantFunctorCompIso T x g).hom =
        constantFunctorHomMap T (e.app x).hom := by
  have h := functorHomEvaluate_constantFunctorHomMap T e.hom x
  change (constantFunctorCompIso T x f).inv ≫
    (SSet.mapHomotopyCategory ((MonoidalClosed.pre (SSet.const x : T ⟶ K)).app X)).map e.hom ≫
      (constantFunctorCompIso T x g).hom = _ at h
  rw [← functorIso_precomp_hom] at h
  have he : functorHomEvaluate e.hom x = (e.app x).hom := by
    rw [FunctorIso.app_eq_evaluate]
    rfl
  rw [he] at h
  exact h

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
