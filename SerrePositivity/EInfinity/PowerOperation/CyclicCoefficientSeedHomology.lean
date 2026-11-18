module

public import SerrePositivity.EInfinity.PowerOperation.CyclicCoefficientSeed
public import SerrePositivity.EInfinity.PowerOperation.CochainZeroCycleClass

/-!
# 指定係数の実鎖写像と同じ周期ホモロジー類

DAG XIII Construction 2.2.6 の係数側の補助。
単位複体から作った同じ実射のホモロジー類を、先に指定した負一次の係数類へ照合する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CochainComplex
open SerrePositivity.DifferentialGraded
variable (p : ℕ) [NeZero p] (k : Type u) [CommRing k] [CharP k p]

/-- 同じ係数種の実 H^0 類は、指定ホモロジー同型で 1 に送られる。 -/
lemma powerOperationCoefficientSeed_homology_value :
    (cyclicResolutionSingleHomologyIso p
      (Rep.trivial k (PowerOperationCyclicGroup.{u} p) k) 0).hom
      (_root_.SerrePositivity.HomologyZero.unitClass (powerOperationCoefficientHomComplex p k)
        (powerOperationCoefficientSeed p k)) = 1 := by
  let H := powerOperationCoefficientHomComplex p k
  let A := Rep.trivial k (PowerOperationCyclicGroup.{u} p) k
  have heq := congrArg (fun f => (zeroCyclesActualIso H).hom ≫ f)
    (cyclicResolutionSingleHomologyIso_pi p A 0)
  simp only [← Category.assoc] at heq
  rw [zeroCyclesActualIso_homologyπ, zeroCyclesActualIso_i] at heq
  have hv := congrArg (fun f => f (cycleFromUnit H (powerOperationCoefficientSeed p k))) heq
  change (cyclicResolutionSingleHomologyIso p A 0).hom
      (_root_.SerrePositivity.HomologyZero.unitClass H (powerOperationCoefficientSeed p k)) =
    cyclicResolutionSingleDegreeEquiv p A 0
      (cycleFromUnit H (powerOperationCoefficientSeed p k)).val at hv
  exact hv.trans (powerOperationCoefficientSeed_value p k)

/-- 同じ実鎖写像の類は、先に固定した周期係数模型の指定負一次類へ送られる。 -/
lemma powerOperationCoefficientSeed_matches_class :
    (cyclicResolutionCoefficientClassIso (k := k) p).hom
      (_root_.SerrePositivity.HomologyZero.unitClass (powerOperationCoefficientHomComplex p k)
        (powerOperationCoefficientSeed p k)) = powerOperationTateCoefficientClass p k := by
  change (powerOperationTateCoefficientHomologyIso p k (-1)).inv
      ((cyclicResolutionSingleHomologyIso p
        (Rep.trivial k (PowerOperationCyclicGroup.{u} p) k) 0).hom
        (_root_.SerrePositivity.HomologyZero.unitClass (powerOperationCoefficientHomComplex p k)
          (powerOperationCoefficientSeed p k))) =
    (powerOperationTateCoefficientHomologyIso p k (-1)).inv 1
  exact congrArg (fun x => (powerOperationTateCoefficientHomologyIso p k (-1)).inv x)
    (powerOperationCoefficientSeed_homology_value p k)

end SerrePositivity.EInfinity.PowerOperation
