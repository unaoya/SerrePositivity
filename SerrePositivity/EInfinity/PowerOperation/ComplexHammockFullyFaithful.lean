module

public import SerrePositivity.EInfinity.PowerOperation.ComplexHammockProbeVertices
public import SerrePositivity.EInfinity.PowerOperation.ComplexHammockPinchedComparison
public import SerrePositivity.EInfinity.PowerOperation.FullyFaithfulEquivalencePrecomposition

/-!
# 既存 D(A) への同じ全複体 hammock 比較の充満忠実性

DAG XIII §2.2 の native な降下の橋。指定 sourceIso で照合済みの実屋根族から
probe の像で検出し、同じ probe 自己同値で全頂点へ延ばす。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded _root_.SerrePositivity.ComplexLimits
open _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open FullFaithfulAndEssentiallySurjectiveFunctors
open scoped Simplicial
variable (A : Type u) [CommRing A]

lemma complexHammockDerivedComparison_afterProbe_fullyFaithful :
    IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.relativeKanHammockNerve (complexRelativeProbeMorphism A) ≫
      complexHammockDerivedComparison A) := by
  intro x y
  rw [pinchedHomMap_comp]
  have hp := (complexHammockProbe_isQCatEquivalence A).isFullyFaithful x y
  have hk : IsWeakHomotopyEquivalence (pinchedHomMap (complexHammockDerivedComparison A)
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.relativeKanHammockNerve (complexRelativeProbeMorphism A)).app (Opposite.op ⦋0⦌) x)
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.relativeKanHammockNerve (complexRelativeProbeMorphism A)).app (Opposite.op ⦋0⦌) y)) := by
    rw [complexHammockProbe_vertex, complexHammockProbe_vertex]
    exact complexHammockDerivedComparison_probe_pinched_weak A (complexHammockOriginalObject A x)
      (_root_.SerrePositivity.ComplexLimits.framedLimitKProjectiveProbe A (complexHammockOriginalObject A y))
  exact hp.comp hk.isSimplicialHomotopyEquivalence

/-- 指定 sourceIso を持つ元の全複体の比較は、全写像空間で充満忠実である。 -/
lemma complexHammockDerivedComparison_fullyFaithful :
    IsFullyFaithful (complexHammockDerivedComparison A) :=
  fullyFaithful_of_equivalence_precomposition (complexHammockProbe_isQCatEquivalence A).choose
    (complexHammockDerivedComparison A) (complexHammockDerivedComparison_afterProbe_fullyFaithful A)

end SerrePositivity.EInfinity.PowerOperation
