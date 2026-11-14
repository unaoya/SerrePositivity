module

public import SerrePositivity.EInfinity.PowerOperation.MayResolution
public import SerrePositivity.EInfinity.BarrattEccles.HomologyCoefficient
public import SerrePositivity.EInfinity.BarrattEccles.Degrees

/-!
# May の D₀ の指定係数

May, Definitions 2.1・2.2 と Proposition 2.3(iii) の零次係数の前段。
同じ W→E(p) の零次を正則生成元に評価し、その増大が 1 であることを証明する。
任意の可換係数環で、選んだ比較射を変更せずに使う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.EInfinity.BarrattEccles
variable (p : ℕ) [NeZero p] (k : Type u) [CommRing k]

/-- W の零次の正則生成元を、同じ指定比較で E(p) へ送る。 -/
def mayZeroCoefficientValue : (complex k p).X 0 :=
  ((mayResolutionComparison p k).f 0).hom (.single 1 1)

/-- 同じ指定比較の零次係数の増大は 1。 -/
lemma mayZeroCoefficientValue_augmentation :
    (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat k))).hom
      ((complexAugmentation k p).f 0 (mayZeroCoefficientValue p k)) = 1 := by
  have h := congrArg (fun f => (f.f 0).hom (.single 1 1))
    (mayResolutionComparison_augmentation p k)
  change (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat k))).hom
      ((complexAugmentation k p).f 0 (mayZeroCoefficientValue p k)) =
    ((mayResolution p k).π.f 0).hom (.single 1 1) at h
  rw [h]
  change (Rep.leftRegularHom (Rep.trivial k (MayCyclicGroup.{u} p) k) 1).hom
    (.single 1 1) = 1
  simp

/-- E(p) の同じ零次係数は実 cycle。 -/
def mayZeroCoefficientCycle : zeroCycles (complex k p) :=
  ⟨mayZeroCoefficientValue p k, by
    rw [LinearMap.mem_ker]
    have h : (complex k p).d 0 1 = 0 :=
      (complex_isZero_positive k p 1 (by omega)).eq_of_tgt _ _
    rw [h]
    rfl⟩

/-- 同じ指定比較の零次係数を表す実複体射。 -/
def mayZeroCoefficient : 𝟙_ (Complex k) ⟶ (operad k).arity p :=
  unitFromCycle _ (mayZeroCoefficientCycle p k)

/-- 指定零次係数を 1 で評価すると、元の比較射の値を回収する。 -/
lemma mayZeroCoefficient_value :
    (cycleFromUnit _ (mayZeroCoefficient p k)).val = mayZeroCoefficientValue p k := by
  rw [mayZeroCoefficient, cycleFromUnit_unitFromCycle]
  rfl

/-- 同じ零次係数は、BE の指定増大を保つ。 -/
lemma mayZeroCoefficient_augmentation :
    mayZeroCoefficient p k ≫ (augmentation k).map.app (FiniteBijection.of p) = 𝟙 _ := by
  change mayZeroCoefficient p k ≫ complexAugmentation k p = 𝟙 (𝟙_ (Complex k))
  apply (unitCycleEquiv (𝟙_ (Complex k))).injective
  apply Subtype.ext
  change (cycleFromUnit _ (mayZeroCoefficient p k ≫ complexAugmentation k p)).val =
    (cycleFromUnit _ (𝟙 (𝟙_ (Complex k)))).val
  rw [cycleFromUnit_postcomp, mayZeroCoefficient_value]
  exact mayZeroCoefficientValue_augmentation p k

/-- 同じ D₀ 係数は、既存の零次 arity 係数と実鎖ホモトピーで比較できる。 -/
def mayZeroCoefficientHomotopy : Homotopy (mayZeroCoefficient p k) (aritySection k p) :=
  coefficientHomotopy k p _ _
    ((mayZeroCoefficient_augmentation p k).trans (aritySection_augmentation k p).symm)

end SerrePositivity.EInfinity.PowerOperation
