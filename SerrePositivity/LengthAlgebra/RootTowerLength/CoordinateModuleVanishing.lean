module

public import SerrePositivity.LengthAlgebra.RootTowerLength.CoordinateVanishing
public import SerrePositivity.LengthAlgebra.RootTowerLength.CompletedNormalized
public import SerrePositivity.LengthAlgebra.AlmostVanishing

/-! # 一座標の全ての根で消える加群の長さ零

巡回商の座標根の評価を、上限性を持つ正規化長さで一般の冪ねじれ加群へ移す。
perfectoid化や、そのイデアルと根の生成イデアルの一致は必要ない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.RootTowerLength
open IsLocalRing Section2

/-- 全ての座標根が零化する冪ねじれ加群は、正規化長さ零。 -/
theorem completedNormalizedLength_module_eq_zero_of_coordinate_roots
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (ht : ∀ j, t j ∈ maximalIdeal A) (hp : (p : A) ∈ maximalIdeal A)
    (i : Fin h) (M : Type u) [AddCommGroup M] [Module (CompletedTower A t p) M]
    (hM : IsPowTorsion (completedTowerMaxIdeal A t p) M)
    (hroots : ∀ n : ℕ, ∀ x : M,
      algebraMap (TowerStage A t p n) (CompletedTower A t p) (stageX A t p n i) • x = 0) :
    (completedNormalizedLength A t p ht).len M = 0 := by
  let L : Ideal (CompletedTower A t p) := Ideal.span (Set.range (fun n : ℕ ↦
    algebraMap (TowerStage A t p n) (CompletedTower A t p) (stageX A t p n i)))
  have hcyclic (a : ℕ) : (completedNormalizedLength A t p ht).len
      (CompletedTower A t p ⧸ ((completedTowerMaxIdeal A t p) ^ a ⊔ L)) = 0 := by
    have hIK : ((maximalIdeal A) ^ a).map (algebraMap A (CompletedTower A t p)) ≤
        (completedTowerMaxIdeal A t p) ^ a ⊔ L := by
      rw [Ideal.map_pow]
      exact le_sup_left
    exact completedNormalizedLength_quotient_eq_zero_of_coordinate_roots A t p ht hp
      ((maximalIdeal A) ^ a) (finiteLength_quotient_maximalIdeal_pow A a) a le_rfl _ hIK i
      (fun n ↦ (le_sup_right : L ≤ _) (Ideal.subset_span ⟨n, rfl⟩))
  have hL : Almost.IsAlmostZero L M := by
    apply Ideal.span_le.mpr
    rintro _ ⟨n, rfl⟩
    exact Module.mem_annihilator.mpr (hroots n)
  exact LengthAlgebra.length_eq_zero_of_cyclic_quotients L _
    (completedNormalizedLength A t p ht) (completedNormalizedLength_hasSup A t p ht)
    hcyclic M hM hL

/-- 差のイデアルを全ての座標根が零化すれば、自然な商間で長さは一致する。 -/
theorem completedNormalizedLength_quotient_pow_eq_of_coordinateRoot_mul
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (ht : ∀ j, t j ∈ maximalIdeal A) (hp : (p : A) ∈ maximalIdeal A)
    (i : Fin h) (I H : Ideal (CompletedTower A t p)) (hIH : I ≤ H)
    (hroots : ∀ m : ℕ, ∀ b ∈ H,
      algebraMap (TowerStage A t p m) (CompletedTower A t p) (stageX A t p m i) * b ∈ I)
    (a : ℕ) :
    (completedNormalizedLength A t p ht).len
      (CompletedTower A t p ⧸ ((completedTowerMaxIdeal A t p) ^ a ⊔ I)) =
    (completedNormalizedLength A t p ht).len
      (CompletedTower A t p ⧸ ((completedTowerMaxIdeal A t p) ^ a ⊔ H)) := by
  let J := completedTowerMaxIdeal A t p
  let f := (Ideal.Quotient.factorₐ (CompletedTower A t p) (sup_le_sup_left hIH (J ^ a))).toLinearMap
  have hsource : IsPowTorsion J (CompletedTower A t p ⧸ (J ^ a ⊔ I)) := by
    refine ⟨a, ?_⟩
    rw [Module.isTorsionBySet_iff_subset_annihilator, SetLike.coe_subset_coe,
      Ideal.annihilator_quotient]
    exact le_sup_left
  have hk : (completedNormalizedLength A t p ht).len (LinearMap.ker f) = 0 := by
    apply completedNormalizedLength_module_eq_zero_of_coordinate_roots A t p ht hp i _
      (hsource.submodule (LinearMap.ker f))
    intro m x
    apply Subtype.ext
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (x : CompletedTower A t p ⧸ (J ^ a ⊔ I))
    have hbH : b ∈ J ^ a ⊔ H := by
      have hx := x.property
      rw [LinearMap.mem_ker, ← hb] at hx
      exact Ideal.Quotient.eq_zero_iff_mem.mp hx
    obtain ⟨j, hj, y, hy, hsum⟩ := Submodule.mem_sup.mp hbH
    change _ • (x : CompletedTower A t p ⧸ (J ^ a ⊔ I)) = 0
    rw [← hb]
    change Ideal.Quotient.mk (J ^ a ⊔ I)
      (algebraMap (TowerStage A t p m) (CompletedTower A t p) (stageX A t p m i) * b) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [← hsum, mul_add]
    exact (J ^ a ⊔ I).add_mem
      ((le_sup_left : J ^ a ≤ J ^ a ⊔ I) ((J ^ a).mul_mem_left _ hj))
      ((le_sup_right : I ≤ J ^ a ⊔ I) (hroots m y hy))
  rw [(completedNormalizedLength A t p ht).len_eq_add_ker_range f hsource,
    hk, zero_add, LinearMap.range_eq_top.mpr
      (Ideal.Quotient.factor_surjective (sup_le_sup_left hIH (J ^ a)))]
  exact (completedNormalizedLength A t p ht).len_congr _ _ Submodule.topEquiv

end SerrePositivity.RootTowerLength
