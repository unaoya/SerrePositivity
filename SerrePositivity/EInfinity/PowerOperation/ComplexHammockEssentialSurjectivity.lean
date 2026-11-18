module

public import SerrePositivity.EInfinity.PowerOperation.ComplexHammockSource
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.SemifreeClosedDerivedComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithful

/-!
# 元の全複体の hammock から D(A) への比較の本質的全射性

DAG XIII §2.2 の native な降下への前段。元の半自由閉零圏上の全関手同型を
同じ頂点に評価する。写像空間の充満忠実性とは区別する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded _root_.SerrePositivity.ComplexLimits
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories
open DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open FullFaithfulAndEssentiallySurjectiveFunctors
variable (A : Type u) [CommRing A]

/-- 半自由な元の複体での比較の値は、同じ元の頂点と同型。 -/
def complexHammockDerivedComparison_valueIso (M : Semifree A) :
    VertexIso ((complexHammockDerivedComparison A).app (Opposite.op ⦋0⦌)
      ((complexHammockSource A).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ (AsSmall.up.{u, u + 1, u + 1}.obj M.val)))) (Simplex.vertex M) := by
  let x := ComposableArrows.mk₀
    (show (complexRelativeCategory A).category from AsSmall.up.{u, u + 1, u + 1}.obj M.val)
  have hx : (complexRelativeNerveDown A).app (Opposite.op ⦋0⦌) x =
      ComposableArrows.mk₀ M.val := ComposableArrows.ext₀ rfl
  have ep : VertexIso ((complexRelativeDerivedSource A).app (Opposite.op ⦋0⦌) x)
      ((_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ M.val)) :=
    eqToIso (congrArg HomotopyCategory.mk
      (congrArg ((_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌)) hx))
  let z : ClosedCategory A (Semifree A) := ForgetEnrichment.of (Complex A) M
  have e := (_root_.SerrePositivity.ComplexLimits.semifreeClosedDerivedSourceIso A).app (ComposableArrows.mk₀ z)
  change VertexIso ((_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌)
    ((nerveMap (semifreeClosedToComplex A)).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ z)))
    ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (Semifree A)).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ z)) at e
  rw [nerveMap_app_mk₀] at e
  have hv : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (Semifree A)).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ z) = Simplex.vertex M := by
    apply (dgNerve.vertexEquiv A (Semifree A)).injective
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion_vertex]
    rfl
  rw [hv] at e
  change VertexIso ((_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌)
    (ComposableArrows.mk₀ M.val)) (Simplex.vertex M) at e
  exact (complexHammockDerivedComparison_sourceIso A).app x ≪≫ ep ≪≫ e

/-- 同じ比較は D(A) の全ての元の半自由頂点を本質的に覆う。 -/
lemma complexHammockDerivedComparison_essentiallySurjective :
    IsEssentiallySurjective (complexHammockDerivedComparison A) := by
  intro y
  obtain ⟨M, rfl⟩ := (Simplex.vertexEquiv (A := A) (D := Semifree A)).symm.surjective y
  exact ⟨(complexHammockSource A).app (Opposite.op ⦋0⦌)
    (ComposableArrows.mk₀ (AsSmall.up.{u, u + 1, u + 1}.obj M.val)),
    ⟨complexHammockDerivedComparison_valueIso A M⟩⟩

end SerrePositivity.EInfinity.PowerOperation
