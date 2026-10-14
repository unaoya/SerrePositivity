module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PairTowerPresentation

/-! # 二座標の三項モデルから完備加群への評価

始値と二つの列の和から評価写像を作り、交差境界を含む全境界の消滅を証明する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable (R : Type u) [CommRing R]

/-- サイクルの始値から二つの列の和を引く線形評価。 -/
def pairTowerCycleEvaluation (f d : R) (N : ModuleCat.{u} R)
    (hf : IsModuleComplete R f N) (hd : IsModuleComplete R d N) (t : N) :
    PairTowerCycles R f d →ₗ[R] N :=
  (((LinearMap.toSpanSingleton R N t).comp (LinearMap.fst R _ _) -
    (completeSequenceSum R d N hd).comp ((sequenceScalarMap R N t).comp
      ((LinearMap.fst R _ _).comp (LinearMap.snd R _ _)))) -
    (completeSequenceSum R f N hf).comp ((sequenceScalarMap R N t).comp
      ((LinearMap.snd R _ _).comp (LinearMap.snd R _ _)))).comp
        (pairTowerCycleCoordinates R f d).toLinearMap

@[simp] theorem pairTowerCycleEvaluation_apply (f d : R) (N : ModuleCat.{u} R)
    (hf : IsModuleComplete R f N) (hd : IsModuleComplete R d N) (t : N)
    (c : PairTowerCycles R f d) :
    pairTowerCycleEvaluation R f d N hf hd t c = c.val.1 0 • t -
      completeSequenceSum R d N hd (sequenceScalarMap R N t c.val.2.1) -
        completeSequenceSum R f N hf (sequenceScalarMap R N t c.val.2.2) := rfl

/-- 係数の漸化式を、指定した元のスカラー倍の漸化式へ移す。 -/
theorem sequenceScalarMap_recurrence (a : R) (N : ModuleCat.{u} R) (t : N)
    (x : ℕ → R) :
    sequenceScalarMap R N t (adicRecurrenceMap a x) =
      adicRecurrenceMap a (sequenceScalarMap R N t x) := by
  funext n
  simp [sequenceScalarMap, adicRecurrenceMap, sub_smul, mul_smul]

/-- 係数の冪による重みを、加群上のスカラー作用へ移す。 -/
theorem sequenceScalarMap_power (a : R) (N : ModuleCat.{u} R) (t : N)
    (x : ℕ → R) :
    sequenceScalarMap R N t (principalPowerMap R a x) =
      fun n ↦ a ^ n • (sequenceScalarMap R N t x n) := by
  funext n
  simp [sequenceScalarMap, principalPowerMap, mul_smul]

/-- 二つの通常の境界と交差境界のすべてが、完備加群への評価で消える。 -/
theorem pairTowerCycleEvaluation_boundary (f d : R) (N : ModuleCat.{u} R)
    (hf : IsModuleComplete R f N) (hd : IsModuleComplete R d N) (t : N)
    (z : ((ℕ → R) × (ℕ → R)) × (ℕ → R)) :
    pairTowerCycleEvaluation R f d N hf hd t (pairTowerBoundary R f d z) = 0 := by
  rw [pairTowerCycleEvaluation_apply]
  change (d ^ 0 * z.1.1 0 + f ^ 0 * z.1.2 0) • t -
    completeSequenceSum R d N hd (sequenceScalarMap R N t
      (adicRecurrenceMap d z.1.1 - principalPowerMap R f z.2)) -
    completeSequenceSum R f N hf (sequenceScalarMap R N t
      (adicRecurrenceMap f z.1.2 + principalPowerMap R d z.2)) = 0
  rw [map_sub, map_add, map_sub, map_add, sequenceScalarMap_recurrence,
    sequenceScalarMap_recurrence, completeSequenceSum_recurrence, completeSequenceSum_recurrence,
    sequenceScalarMap_power, sequenceScalarMap_power, completeSequenceSum_cross R f d N hf hd]
  simp [sequenceScalarMap, add_smul]

/-- 境界を消す評価を、サイクルの商へ降ろす。 -/
def pairTowerQuotientEvaluation (f d : R) (N : ModuleCat.{u} R)
    (hf : IsModuleComplete R f N) (hd : IsModuleComplete R d N) (t : N) :
    (PairTowerCycles R f d ⧸ (pairTowerBoundary R f d).range) →ₗ[R] N :=
  (pairTowerBoundary R f d).range.liftQ (pairTowerCycleEvaluation R f d N hf hd t) (by
    rintro c ⟨z, rfl⟩
    exact pairTowerCycleEvaluation_boundary R f d N hf hd t z)

/-- 定数サイクルは、指定したスカラー倍へ送られる。 -/
theorem pairTowerQuotientEvaluation_unit (f d : R) (N : ModuleCat.{u} R)
    (hf : IsModuleComplete R f N) (hd : IsModuleComplete R d N) (t : N) (r : R) :
    pairTowerQuotientEvaluation R f d N hf hd t
      (Submodule.Quotient.mk (pairTowerConstantCycle R f d r)) = r • t := by
  change pairTowerCycleEvaluation R f d N hf hd t (pairTowerConstantCycle R f d r) = _
  rw [pairTowerCycleEvaluation_apply, pairTowerConstantCycle_val]
  simp

/-- 三項モデルの実際のホモロジーから、完備加群への線形評価。 -/
def pairTowerHomologyEvaluation (f d : R) (N : ModuleCat.{u} R)
    (hf : IsModuleComplete R f N) (hd : IsModuleComplete R d N) (t : N) :
    (pairTowerShortComplex R f d).homology →ₗ[R] N :=
  (pairTowerQuotientEvaluation R f d N hf hd t).comp
    (pairTowerShortComplex R f d).moduleCatHomologyIso.hom.hom

/-- ホモロジーの評価も、標準写像を指定したスカラー倍へ送る。 -/
theorem pairTowerHomologyEvaluation_unit (f d : R) (N : ModuleCat.{u} R)
    (hf : IsModuleComplete R f N) (hd : IsModuleComplete R d N) (t : N) (r : R) :
    pairTowerHomologyEvaluation R f d N hf hd t (pairTowerHomologyUnit R f d r) =
      r • t := by
  let S := pairTowerShortComplex R f d
  let c := pairTowerConstantCycle R f d r
  have h := congrArg (fun g ↦ g.hom (S.moduleCatCyclesIso.inv c))
    S.π_moduleCatCyclesIso_hom
  change S.moduleCatHomologyIso.hom (S.homologyπ (S.moduleCatCyclesIso.inv c)) =
    Submodule.Quotient.mk (S.moduleCatCyclesIso.hom (S.moduleCatCyclesIso.inv c)) at h
  have hi := congrArg (fun g ↦ g.hom c) S.moduleCatCyclesIso.inv_hom_id
  change S.moduleCatCyclesIso.hom (S.moduleCatCyclesIso.inv c) = c at hi
  rw [hi] at h
  change pairTowerQuotientEvaluation R f d N hf hd t
    (S.moduleCatHomologyIso.hom (S.homologyπ (S.moduleCatCyclesIso.inv c))) = _
  rw [h]
  exact pairTowerQuotientEvaluation_unit R f d N hf hd t r

/-- 任意の標準元の像を持つ、三項モデルのH⁰からの延長が存在する。 -/
theorem pairTowerHomologyEvaluation_exists (f d : R) (N : ModuleCat.{u} R)
    (hf : IsModuleComplete R f N) (hd : IsModuleComplete R d N) (t : N) :
    ∃ g : (pairTowerShortComplex R f d).homology →ₗ[R] N,
      g (pairTowerHomologyUnit R f d 1) = t := by
  refine ⟨pairTowerHomologyEvaluation R f d N hf hd t, ?_⟩
  rw [pairTowerHomologyEvaluation_unit, one_smul]

end SerrePositivity.DerivedCompletion
