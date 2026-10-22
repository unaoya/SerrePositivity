module
public import SerrePositivity.InfinityCategories.Stable.LoopSectionEvaluation
public import SerrePositivity.InfinityCategories.Derived.QCatEquivalenceAdjunction
public import SerrePositivity.InfinityCategories.F1B.PointwiseUnitComparison
public import SerrePositivity.InfinityCategories.F1B.UnitCommaInitialFromMapping
/-!
概要：loop 始点評価の逆による実随伴と comma の普遍単位。
方針：元の同値を三角式付き随伴へ移し、全写像空間の単位条件を使う。
規約：全錐側の同値性は別工程。使われ方：一般安定性判定の始対象の供給。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {X : SSet.{u}} [Quasicategory X] [HasZeroVertex X]
variable (s : X ⟶ loopDiagrams X) (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
variable (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0))
def loopSourceInverse : X ⟶ loopDiagrams X :=
  (loopDiagramEvaluation_source_isQCatEquivalence_of_loopEquivalence s hs hΩ).choose.inv
def loopSourceAdjunction : QCatAdjunction (loopSourceInverse s hs hΩ)
    (loopDiagramEvaluation X 0 0) :=
  let e := (loopDiagramEvaluation_source_isQCatEquivalence_of_loopEquivalence s hs hΩ).choose
  e.symm.toAdjunction
def loopSourceUnit : FunctorHom (𝟙 X)
    (loopSourceInverse s hs hΩ ≫ loopDiagramEvaluation X 0 0) :=
  (loopSourceAdjunction s hs hΩ).unitHom
lemma loopSourceUnit_initial (x : X _⦋0⦌) :
    IsInitialVertex (unitCommaSectionVertex (loopSourceUnit s hs hΩ) x) := by
  apply (unitCommaInitialCondition_iff (loopSourceUnit s hs hΩ)).mp
    (loopSourceAdjunction s hs hΩ).unitMappingSpaceCondition.unitCommaInitialCondition
end SerrePositivity.InfinityCategories
