module

public import SerrePositivity.CommutativeAlgebra.RootTower.Completion
public import SerrePositivity.CommutativeAlgebra.RootTower.Stage
public import SerrePositivity.CommutativeAlgebra.FrobeniusRootKernels

/-! # 完備した根の塔の座標と両立する冪根

有限段の座標を完備塔へ移し、冪と段の遷移との両立を証明する。
perfectoid性・perfectoid化・長さの引用は使用しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.Section2
variable (A : Type u) [CommRing A] {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]

/-- 有限段の根の座標を完備塔へ移した元。 -/
def completedTowerRoot (n : ℕ) (i : Fin h) : CompletedTower A t p :=
  algebraMap (TowerStage A t p n) (CompletedTower A t p) (stageX A t p n i)

omit [Fact p.Prime] in
/-- 完備塔の根の座標の `p^n` 乗は、基底環の対応する座標の標準像である。 -/
@[simp] theorem completedTowerRoot_pow (n : ℕ) (i : Fin h) :
    completedTowerRoot A t p n i ^ (p ^ n) =
      algebraMap A (CompletedTower A t p) (t i) := by
  rw [completedTowerRoot, ← map_pow]
  change algebraMap (TowerStage A t p n) (CompletedTower A t p)
    (Ideal.Quotient.mk (towerRel A t p n) (MvPolynomial.X i) ^ (p ^ n)) = _
  rw [mk_X_pow, ← IsScalarTower.algebraMap_apply A (TowerStage A t p n) (CompletedTower A t p)]

omit [Fact p.Prime] in
/-- 根の座標は、段を進めるとp乗によって元の座標に戻る。 -/
@[simp] theorem completedTowerRoot_succ_pow (n : ℕ) (i : Fin h) :
    completedTowerRoot A t p (n + 1) i ^ p = completedTowerRoot A t p n i := by
  have hstage : towerMap A t p n (n + 1) (Nat.le_succ n) (stageX A t p n i) =
      stageX A t p (n + 1) i ^ p := by
    simpa using towerMap_mk_X A t p n (n + 1) (Nat.le_succ n) i
  have htower := congrArg (algebraMap (Tower A t p) (CompletedTower A t p))
    (towerOf_towerMap A t p n (n + 1) (Nat.le_succ n) (stageX A t p n i))
  rw [hstage, map_pow] at htower
  exact htower

omit [Fact p.Prime] in
/-- 初段の座標は、基底環の対応する元の像である。 -/
@[simp] theorem completedTowerRoot_zero (i : Fin h) :
    completedTowerRoot A t p 0 i = algebraMap A (CompletedTower A t p) (t i) := by
  simpa using completedTowerRoot_pow A t p 0 i

omit [Fact p.Prime] in
/-- n段の根をm段で表すとき、指数はp^(m-n)になる。 -/
theorem completedTowerRoot_pow_of_le (n m : ℕ) (hnm : n ≤ m) (i : Fin h) :
    completedTowerRoot A t p m i ^ (p ^ (m - n)) = completedTowerRoot A t p n i := by
  have heq := compatibleRoots_pow p (fun l ↦ completedTowerRoot A t p l i)
    (fun l ↦ completedTowerRoot_succ_pow A t p l i) n (m - n)
  simpa only [Nat.add_sub_of_le hnm] using heq

omit [Fact p.Prime] in
/-- pを座標に含めれば、完備塔ではpそのものがp乗である。 -/
theorem exists_completedTower_p_root (i : Fin h) (hti : t i = (p : A)) :
    ∃ π : CompletedTower A t p, (p : CompletedTower A t p) = π ^ p := by
  refine ⟨completedTowerRoot A t p 1 i, ?_⟩
  have hh := completedTowerRoot_pow A t p 1 i
  simpa only [pow_one, hti, map_natCast] using hh.symm

end SerrePositivity.Section2
