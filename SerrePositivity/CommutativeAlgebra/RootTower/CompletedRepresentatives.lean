module

public import SerrePositivity.CommutativeAlgebra.RootTower.Completion
public import SerrePositivity.CommutativeAlgebra.Adic.Completion.Basic

/-! # 完備塔の元の有限段での代表

完備化の冪商の比較と有向極限の有限性から、完備塔の有限個の元を
任意のp冪を法として共通の有限段で代表する。perfectoid性やNoether性は不要。
-/

@[expose] public noncomputable section
universe u
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
