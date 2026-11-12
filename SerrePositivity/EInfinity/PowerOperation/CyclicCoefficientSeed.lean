module

public import SerrePositivity.EInfinity.PowerOperation.CyclicResolutionHomNaturality
public import SerrePositivity.DifferentialGraded.Complexes.HomComplex

/-!
# 指定周期係数類を表す実鎖写像

DAG XIII Construction 2.2.6 の係数類の鎖レベルの前段。
同じ左正則評価で 1 に対応する零次 cycle を取り、単位複体からの実射を作る。
これは係数模型の射であり、T_p のスペクトル的な右 k 作用との比較はまだ含めない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CochainComplex MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (p : ℕ) [NeZero p] (k : Type u) [CommRing k] [CharP k p]

/-- 同じ自明係数 k における完全周期 Hom 複体。 -/
abbrev powerOperationCoefficientHomComplex : Complex k :=
  linearHomComplex k (powerOperationCompleteResolution p k)
    ((singleFunctor (Rep.{u} k (PowerOperationCyclicGroup.{u} p)) 0).obj
      (Rep.trivial k (PowerOperationCyclicGroup.{u} p) k))

/-- 同じ指定評価で 1 に対応する実零次 cycle。 -/
def powerOperationCoefficientCycle : zeroCycles (powerOperationCoefficientHomComplex p k) :=
  ⟨(cyclicResolutionSingleDegreeEquiv p
      (Rep.trivial k (PowerOperationCyclicGroup.{u} p) k) 0).symm (1 : k), by
    rw [LinearMap.mem_ker]
    change ((powerOperationCoefficientHomComplex p k).d 0 1).hom _ = 0
    rw [cyclicResolutionSingleHom_d p
      (Rep.trivial k (PowerOperationCyclicGroup.{u} p) k) 0 1]
    rfl⟩

/-- 指定係数 cycle を表す、単位複体からの実鎖写像。 -/
def powerOperationCoefficientSeed :
    𝟙_ (Complex k) ⟶ powerOperationCoefficientHomComplex p k :=
  unitFromCycle _ (powerOperationCoefficientCycle p k)

/-- 同じ鎖写像を 1 で評価すると、指定係数 1 を正確に回収する。 -/
lemma powerOperationCoefficientSeed_value :
    cyclicResolutionSingleDegreeEquiv p
      (Rep.trivial k (PowerOperationCyclicGroup.{u} p) k) 0
      (cycleFromUnit _ (powerOperationCoefficientSeed p k)).val = 1 := by
  rw [powerOperationCoefficientSeed, cycleFromUnit_unitFromCycle]
  exact (cyclicResolutionSingleDegreeEquiv p
    (Rep.trivial k (PowerOperationCyclicGroup.{u} p) k) 0).apply_symm_apply _

end SerrePositivity.EInfinity.PowerOperation
