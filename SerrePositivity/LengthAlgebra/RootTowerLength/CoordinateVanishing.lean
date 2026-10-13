module

public import SerrePositivity.LengthAlgebra.RootTowerLength.CoordinateQuotientLength
public import SerrePositivity.LengthAlgebra.GeometricDecay

/-! # 一座標の全ての根を含む商の長さ零

有限長な基底商と、一座標の全ての根を含む完備塔の商について、
有限段の単項式の長さ上界を幾何的減衰の一般論へ渡す。
perfectoid 化やその被約性はこの数値定理に要求しない。
-/

@[expose] public noncomputable section
universe u
open scoped TensorProduct ENNReal
namespace SerrePositivity.RootTowerLength
open Section2 IsLocalRing
set_option backward.isDefEq.respectTransparency false

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (ht : ∀ j, t j ∈ maximalIdeal A) (hp : (p : A) ∈ maximalIdeal A)

include hp in
/-- 一座標の全ての根と有限長な基底商の関係式を含む商は、正規化長さが零。 -/
theorem completedNormalizedLength_quotient_eq_zero_of_coordinate_roots
    (I : Ideal A) (hfinite : IsFiniteLength A (A ⧸ I)) (n : ℕ)
    (hJI : (maximalIdeal A) ^ n ≤ I) (K : Ideal (CompletedTower A t p))
    (hIK : I.map (algebraMap A (CompletedTower A t p)) ≤ K) (i : Fin h)
    (hroots : ∀ m : ℕ, algebraMap (TowerStage A t p m) (CompletedTower A t p)
      (stageX A t p m i) ∈ K) :
    (completedNormalizedLength A t p ht).len (CompletedTower A t p ⧸ K) = 0 := by
  let C := CompletedTower A t p
  let H (m : ℕ) : Ideal (TowerStage A t p m) :=
    I.map (algebraMap A (TowerStage A t p m)) ⊔ Ideal.span {stageX A t p m i}
  let L (m : ℕ) := (H m).map (algebraMap (TowerStage A t p m) C)
  have hIMap (m : ℕ) : I.map (algebraMap A C) ≤ L m := by
    have hm := Ideal.map_mono (f := algebraMap (TowerStage A t p m) C)
      (show I.map (algebraMap A (TowerStage A t p m)) ≤ H m from le_sup_left)
    simpa only [Ideal.map_map, ← IsScalarTower.algebraMap_eq] using hm
  have hpow (m : ℕ) : (completedTowerMaxIdeal A t p) ^ n ≤ L m := by
    have hbase : (completedTowerMaxIdeal A t p) ^ n ≤ I.map (algebraMap A C) := by
      simpa only [completedTowerMaxIdeal, ← Ideal.map_pow] using
        Ideal.map_mono (f := algebraMap A C) hJI
    exact hbase.trans (hIMap m)
  have hLK (m : ℕ) : L m ≤ K := by
    dsimp only [L, H]
    rw [Ideal.map_sup, Ideal.map_map, ← IsScalarTower.algebraMap_eq,
      Ideal.map_span, Set.image_singleton]
    exact sup_le hIK ((K.span_singleton_le_iff_mem).mpr (hroots m))
  have hb (m : ℕ) : (completedNormalizedLength A t p ht).len (C ⧸ L m) ≤
      (Module.length A (A ⧸ I) : ℝ≥0∞) / (p : ℝ≥0∞) ^ m := by
    simpa only [Nat.cast_pow] using
      completedNormalizedLength_coordinateQuotient_le A t p ht hp m I hfinite
        i (H m) le_sup_left
        ((le_sup_right : Ideal.span {stageX A t p m i} ≤ H m)
          (Ideal.subset_span (Set.mem_singleton _)))
  exact (completedNormalizedLength A t p ht).len_quotient_eq_zero_of_div_pow_covers
    n K L hpow hLK (Module.length A (A ⧸ I) : ℝ≥0∞) (p : ℝ≥0∞)
    (ENat.toENNReal_ne_top.mpr (Module.length_ne_top_iff.mpr hfinite))
    (by exact_mod_cast (Fact.out : p.Prime).one_lt) hb

end SerrePositivity.RootTowerLength
