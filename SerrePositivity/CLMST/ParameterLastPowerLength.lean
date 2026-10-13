module

public import SerrePositivity.CLMST.CompletedParameterFiniteness
public import SerrePositivity.LengthAlgebra.KoszulEulerZero
public import SerrePositivity.CommutativeAlgebra.ParameterLastPower

/-! # CLMST Claim 4.0.15：最後のパラメータの冪による長さの倍率

全パラメータ系の長さの有限性と負次数の長さ消滅を別々に適用し、
共通の Koszul Euler 評価の冪の倍率を正規化長さの倍率へ戻す。
Proposition 4.0.14 の長さ公式そのものを入力として使わない。
-/

@[expose] public noncomputable section
universe u
open scoped TensorProduct ENNReal
namespace SerrePositivity.CLMST
open Section2 IsLocalRing CategoryTheory

variable (A D : Type u) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [IsDomain D]
    [IsAdicComplete (maximalIdeal D) D] [Algebra A D] [Module.Finite A D]
    (hinj : Function.Injective (algebraMap A D))
    (hres : Function.Surjective ((residue D).comp (algebraMap A D)))
    {h : ℕ} (t : Fin h → A) (hdimA : ringKrullDim A = h) (hdimD : ringKrullDim D = h)
    (hpos : 0 < h) (ht : Ideal.span (Set.range t) = maximalIdeal A)
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t))
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField D) p] [PerfectField (ResidueField D)]
    [CharZero D] (htp : t ⟨0, hpos⟩ = (p : A))
    (e : A ≃+* MvPowerSeries {i : Fin h // (i : ℕ) ≠ 0} (WittVector p (ResidueField D)))
    (he : ∀ (i : Fin h) (hi : (i : ℕ) ≠ 0), e (t i) = MvPowerSeries.X ⟨i, hi⟩)
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)

local instance : Module.FinitePresentation A D := Module.finitePresentation_of_finite A D

include hinj hres hdimA hdimD hpos ht hsop htp e he

set_option maxHeartbeats 600000 in
-- 二つの大きな係数モデルと各正冪の有限性を照合するため、型検査の予算を増やす。
/-- 有限段のパラメータ系の最後を正の k 乗にすると、係数 Koszul モデルの零次長さは k 倍。
引用からの高次消滅、独立に証明した有限性、共通の Euler 倍率を組み合わせる。 -/
theorem completedTensor_stage_parameter_last_pow_length
    (g : A) (hg : g ≠ 0)
    (hEtale : let _ := GenericEtale.awayAlgebra A D g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap A D g)))
    (n : ℕ) {r : ℕ} (hr : h = r + 1) (y : Fin (r + 1) → StageAlgebra A D t p n)
    (hy : let _ := stageAlgebra_isLocalRing_of_parameters A D t p hsop n
      IsSystemOfParameters (StageAlgebra A D t p n) y) (k : ℕ) (hk : 0 < k) :
    let lam := completedTensorLength A D t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))
    let φ := (stageToCompletedTensor A D t p n).toRingHom
    let S := (CompletedTower A t p) ⊗[A] D
    let M := ModuleCat.of S (RPerfd A D t p hperf)
    lam.len (((koszulModuleFunctor
      (φ ∘ Fin.snoc (Fin.init y) (y (Fin.last r) ^ k))).obj M).homology 0) =
      (k : ℝ≥0∞) * lam.len (((koszulModuleFunctor (φ ∘ y)).obj M).homology 0) := by
  subst h
  let : IsLocalRing (StageAlgebra A D t p n) :=
    stageAlgebra_isLocalRing_of_parameters A D t p hsop n
  let lam := completedTensorLength A D t p
    (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))
  let φ := (stageToCompletedTensor A D t p n).toRingHom
  let S := (CompletedTower A t p) ⊗[A] D
  let M := ModuleCat.of S (RPerfd A D t p hperf)
  let w := φ ∘ y
  have hmap (j : ℕ) : φ ∘ Fin.snoc (Fin.init y) (y (Fin.last r) ^ j) =
      Fin.snoc (Fin.init w) (w (Fin.last r) ^ j) := by
    rw [Fin.comp_snoc]
    congr 1
    exact φ.map_pow _ _
  have hfinite (j : ℕ) (hj : 0 < j) (q : ℤ) :
      lam.len (((koszulModuleFunctor (Fin.snoc (Fin.init w)
        (w (Fin.last r) ^ j))).obj M).homology q) ≠ ⊤ := by
    have hh := completedTensor_stage_parameter_length_ne_top A D hinj hres t hdimA hdimD
      hpos ht hsop p htp e he hperf n _ (hy.pow_last j hj) q
    rw [hmap j] at hh
    exact hh
  have hnegative (j : ℕ) (hj : 0 < j) (q : ℤ) (hq : q < 0) :
      lam.len (((koszulModuleFunctor (Fin.snoc (Fin.init w)
        (w (Fin.last r) ^ j))).obj M).homology q) = 0 := by
    have hh := completedTensor_stage_target_koszul_length_eq_zero A D hinj hres t hdimA hdimD
      hpos ht hsop p htp e he hperf g hg hEtale n _ (hy.pow_last j hj) q hq
    rw [hmap j] at hh
    exact hh
  have htor (j : ℕ) (hj : 0 < j) (q : ℤ) :
      IsPowTorsion (completedTensorMaxIdeal A D t p)
        (((koszulModuleFunctor (Fin.snoc (Fin.init w)
          (w (Fin.last r) ^ j))).obj M).homology q) := by
    have hJ := completedTensorMaxIdeal_le_stage_parameter_radical A D t p n
      (by
        rw [IsScalarTower.algebraMap_eq A D (StageAlgebra A D t p n)]
        exact (stageAlgebra_algebraMap_injective A D t p n).comp hinj)
      _ (hy.pow_last j hj)
    rw [hmap j] at hJ
    exact isPowTorsion_koszulModuleHomology (completedTensorMaxIdeal_fg A D t p)
      _ hJ M q
  have he := length_koszulModule_zero_last_pow lam (Fin.init w) (w (Fin.last r))
    M htor hfinite hnegative k hk
  change lam.len (((koszulModuleFunctor
    (φ ∘ Fin.snoc (Fin.init y) (y (Fin.last r) ^ k))).obj M).homology 0) =
      (k : ℝ≥0∞) * lam.len (((koszulModuleFunctor w).obj M).homology 0)
  rw [Fin.snoc_init_self] at he
  rw [hmap k]
  exact he

set_option maxHeartbeats 600000 in
-- 係数制限の二つの作用と具体的な商の型を照合するため、型検査の予算を増やす。
/-- CLMST Claim 4.0.15 の実際の商の形：最後のパラメータの正冪により長さは指数倍。
長さは完備塔上で測り、商への作用と有限段からの写像を明示する。 -/
theorem completedTower_stage_parameter_quotient_last_pow_length
    (g : A) (hg : g ≠ 0)
    (hEtale : let _ := GenericEtale.awayAlgebra A D g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap A D g)))
    (n : ℕ) {r : ℕ} (hr : h = r + 1) (y : Fin (r + 1) → StageAlgebra A D t p n)
    (hy : let _ := stageAlgebra_isLocalRing_of_parameters A D t p hsop n
      IsSystemOfParameters (StageAlgebra A D t p n) y) (k : ℕ) (hk : 0 < k) :
    let C := RPerfd A D t p hperf
    let φ := (toRPerfd A D t p hperf n).toRingHom
    let Qpow := C ⧸ Ideal.span
      (Set.range (φ ∘ Fin.snoc (Fin.init y) (y (Fin.last r) ^ k)))
    let Q := C ⧸ Ideal.span (Set.range (φ ∘ y))
    let _ := Module.compHom Qpow (algebraMap (CompletedTower A t p) C)
    let _ := Module.compHom Q (algebraMap (CompletedTower A t p) C)
    let lam := RootTowerLength.completedNormalizedLength A t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))
    lam.len Qpow = (k : ℝ≥0∞) * lam.len Q := by
  have hh := completedTensor_stage_parameter_last_pow_length A D hinj hres t hdimA hdimD
    hpos ht hsop p htp e he hperf g hg hEtale n hr y hy k hk
  dsimp only [completedTensorLength] at hh
  rw [LengthAlgebra.length_comap_koszulModuleHomology_zero_quotient,
    LengthAlgebra.length_comap_koszulModuleHomology_zero_quotient] at hh
  have hseq (v : Fin (r + 1) → StageAlgebra A D t p n) :
      algebraMap ((CompletedTower A t p) ⊗[A] D) (RPerfd A D t p hperf) ∘
        ((stageToCompletedTensor A D t p n).toRingHom ∘ v) =
        (toRPerfd A D t p hperf n).toRingHom ∘ v := by
    funext j
    exact stageToCompletedTensor_toMixedPerfectoid A D t p hperf n (v j)
  rw [hseq, hseq] at hh
  exact hh

end SerrePositivity.CLMST
