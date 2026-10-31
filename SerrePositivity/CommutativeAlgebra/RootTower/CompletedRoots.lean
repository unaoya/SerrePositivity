module

public import SerrePositivity.CommutativeAlgebra.RootTower.Completion
public import SerrePositivity.CommutativeAlgebra.RootTower.Stage
public import SerrePositivity.CommutativeAlgebra.Perfection
public import SerrePositivity.CommutativeAlgebra.Adic.Completion.Basic

/-! # 完備塔の座標・冪根と有限段での代表

## 概要

有限段の根の座標を完備塔へ移し、冪と段の遷移との両立を示す。完備化の冪商の比較と有向極限の有限性から、完備塔の有限個の元を任意の p 冪を法として共通の有限段で代表する。

## 方針

座標は有限段からの標準写像の像として定め、代表は `AdicCompletion` の冪商が有限段の有向極限であることから取る。

## 規約

perfectoid 性・perfectoid 化・長さの引用・Noether 性は使わない。名前空間は `SerrePositivity.Section2`。

## 使われ方

CLMST の perfectoid イデアルの根と Frobenius の比較、`RootTower/Perfectoid`。
-/

@[expose] public noncomputable section

universe u

section CompletedRootsPart

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

end SerrePositivity.Section2

end CompletedRootsPart

section CompletedRepresentativesPart

namespace SerrePositivity.Section2
variable (A : Type u) [CommRing A] {h : ℕ} (t : Fin h → A) (p : ℕ)

/-- 有限段から完備塔への写像は塔の遷移写像と両立する。 -/
theorem completedTower_algebraMap_towerMap (a b : ℕ) (hab : a ≤ b)
    (z : TowerStage A t p a) :
    algebraMap (TowerStage A t p b) (CompletedTower A t p) (towerMap A t p a b hab z) =
      algebraMap (TowerStage A t p a) (CompletedTower A t p) z := by
  exact congrArg (algebraMap (Tower A t p) (CompletedTower A t p))
    (towerOf_towerMap A t p a b hab z)

/-- 完備化への写像は、p冪イデアルへの所属を反映する。 -/
theorem completedTower_algebraMap_mem_p_pow_iff (n : ℕ) (r : Tower A t p) :
    algebraMap (Tower A t p) (CompletedTower A t p) r ∈
      Ideal.span {(p : CompletedTower A t p)} ^ n ↔
      r ∈ Ideal.span {(p : Tower A t p)} ^ n := by
  simpa only [Ideal.map_pow, Ideal.map_span, Set.image_singleton, map_natCast] using
    adicCompletion_algebraMap_mem_map_pow_iff (Ideal.span {(p : Tower A t p)})
      (Submodule.fg_span_singleton _) n r

/-- 完備塔の有限個の元をp^kを法として同時に、指定した段以降の共通段で代表する。 -/
theorem exists_completedTower_stage_representatives {ι : Type*} [Finite ι]
    (x : ι → CompletedTower A t p) (k m₀ : ℕ) :
    ∃ (m : ℕ) (_ : m₀ ≤ m) (z : ι → TowerStage A t p m),
      ∀ i, algebraMap (TowerStage A t p m) (CompletedTower A t p) (z i) - x i ∈
        Ideal.span {(p : CompletedTower A t p)} ^ k := by
  have hrep (i : ι) : ∃ r : Tower A t p,
      algebraMap (Tower A t p) (CompletedTower A t p) r - x i ∈
        Ideal.span {(p : CompletedTower A t p)} ^ k := by
    simpa only [Ideal.map_pow, Ideal.map_span, Set.image_singleton, map_natCast] using
      exists_adicCompletion_algebraMap_sub_mem (Ideal.span {(p : Tower A t p)})
        (Submodule.fg_span_singleton _) k (x i)
  choose r hr using hrep
  obtain ⟨m, z, hz⟩ := exists_towerOf_family A t p r
  refine ⟨max m₀ m, le_max_left _ _,
    fun i ↦ towerMap A t p m (max m₀ m) (le_max_right _ _) (z i), fun i ↦ ?_⟩
  rw [completedTower_algebraMap_towerMap]
  change algebraMap (Tower A t p) (CompletedTower A t p) (towerOf A t p m (z i)) - x i ∈ _
  rw [hz]
  exact hr i

/-- 単一の元の、指定した段以降の有限段での代表。 -/
theorem exists_completedTower_stage_representative
    (x : CompletedTower A t p) (k m₀ : ℕ) :
    ∃ (m : ℕ) (_ : m₀ ≤ m) (z : TowerStage A t p m),
      algebraMap (TowerStage A t p m) (CompletedTower A t p) z - x ∈
        Ideal.span {(p : CompletedTower A t p)} ^ k := by
  obtain ⟨m, hm, z, hz⟩ := exists_completedTower_stage_representatives A t p
    (fun _ : Unit ↦ x) k m₀
  exact ⟨m, hm, z (), hz ()⟩

/-- 有限段の元が完備塔でp冪イデアルに入れば、十分先の有限段でもその所属が成立する。
段写像の単射性は不要であり、等式が有向極限で零になることから先の段へ進める。 -/
theorem exists_towerMap_mem_p_pow_of_completed (n k : ℕ) (z : TowerStage A t p n)
    (hz : algebraMap (TowerStage A t p n) (CompletedTower A t p) z ∈
      Ideal.span {(p : CompletedTower A t p)} ^ k) :
    ∃ (m : ℕ) (hnm : n ≤ m),
      towerMap A t p n m hnm z ∈ Ideal.span {(p : TowerStage A t p m)} ^ k := by
  have hzTower : towerOf A t p n z ∈ Ideal.span {(p : Tower A t p)} ^ k :=
    (completedTower_algebraMap_mem_p_pow_iff A t p k _).mp hz
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hzTower
  obtain ⟨b, hb⟩ := hzTower
  obtain ⟨l, w, hw⟩ := exists_towerOf A t p b
  let m := max n l
  let z' := towerMap A t p n m (le_max_left _ _) z
  let w' := towerMap A t p l m (le_max_right _ _) w
  have heq : towerOf A t p m (z' - (p : TowerStage A t p m) ^ k * w') = 0 := by
    simp only [map_sub, map_mul, map_pow, map_natCast, z', w', towerOf_towerMap, hw]
    rw [← hb, sub_self]
  obtain ⟨s, hms, hs⟩ := exists_towerMap_eq_zero A t p m
    (fun _ : Unit ↦ z' - (p : TowerStage A t p m) ^ k * w') (fun _ ↦ heq)
  refine ⟨s, (le_max_left n l).trans hms, ?_⟩
  have hs' : towerMap A t p m s hms z' =
      (p : TowerStage A t p s) ^ k * towerMap A t p m s hms w' := by
    apply sub_eq_zero.mp
    simpa only [map_sub, map_mul, map_pow, map_natCast] using hs ()
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  refine ⟨towerMap A t p m s hms w', ?_⟩
  rw [← towerMap_towerMap A t p n m s (le_max_left _ _) hms]
  exact hs'

end SerrePositivity.Section2

end CompletedRepresentativesPart
