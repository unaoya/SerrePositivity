module

public import SerrePositivity.LengthAlgebra.RootTowerLength.Completion
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.RingTheory.TensorProduct.Quotient
public import SerrePositivity.LengthAlgebra.QuotientBounds
public import SerrePositivity.LengthAlgebra.Almost

/-! # 一つの根座標で消える加群の長さ零

## 概要

一つの根座標を零にした有限段の商の通常の長さを簡約単項式の数（q^(h-1) 以下）で抑え、一座標の全ての根を含む完備塔の商の長さ零を幾何的減衰の一般論から導き、上限性を持つ正規化長さで一般の冪ねじれ加群へ移す。

## 方針

有限段の単項式の長さの上界を `LengthAlgebra/QuotientBounds` の幾何的減衰へ渡す。

## 規約

perfectoid 化やその被約性は要求しない。

## 使われ方

CLMST の正規化長さの消滅（Proposition 4.0.10 の周辺）。
-/

@[expose] public noncomputable section

universe u v

section CoordinateQuotientLengthPart

open scoped TensorProduct ENNReal
namespace SerrePositivity.RootTowerLength
open Section2 IsLocalRing MvPolynomial
set_option backward.isDefEq.respectTransparency false

/-- I で零化され、有限個の元で生成される加群の長さの一般的な上界。 -/
theorem length_le_card_mul_quotient_of_span
    (A : Type u) [CommRing A] (I : Ideal A) (M : Type u)
    [AddCommGroup M] [Module A M] {ι : Type v} [Fintype ι]
    (v : ι → M) (hspan : Submodule.span A (Set.range v) = ⊤)
    (hann : Module.IsTorsionBySet A M I) :
    Module.length A M ≤ Fintype.card ι * Module.length A (A ⧸ I) := by
  let : Module (A ⧸ I) M := hann.module
  let : IsScalarTower A (A ⧸ I) M := hann.isScalarTower
  let F := Finsupp.linearCombination (A ⧸ I) v
  have hs : Submodule.span (A ⧸ I) (Set.range v) = ⊤ := by
    apply top_unique
    intro x hxTop
    clear hxTop
    have hx : x ∈ Submodule.span A (Set.range v) := hspan.symm ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span hx
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [← hann.mk_smul a x]
      exact Submodule.smul_mem _ _ hx
  have hF : Function.Surjective F := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact hs
  have hl := Module.length_le_of_surjective (F.restrictScalars A) hF
  simpa only [Module.length_finsupp, ENat.card_eq_coe_fintype_card] using hl

/-- 残る座標の指数から、指定座標を指数零にした簡約指数を作る。 -/
def coordinateZeroExponent {h q : ℕ} (hq : 0 < q) (i : Fin h)
    (e : {j : Fin h // j ≠ i} → Fin q) : Fin h → Fin q :=
  fun j => if hj : j = i then ⟨0, hq⟩ else e ⟨j, hj⟩

@[simp] theorem coordinateZeroExponent_at {h q : ℕ} (hq : 0 < q) (i : Fin h)
    (e : {j : Fin h // j ≠ i} → Fin q) : (coordinateZeroExponent hq i e i : ℕ) = 0 := by
  simp [coordinateZeroExponent]

/-- 残る簡約指数の個数。 -/
theorem card_coordinateZeroExponent {h q : ℕ} (i : Fin h) :
    Fintype.card ({j : Fin h // j ≠ i} → Fin q) = q ^ (h - 1) := by
  classical
  rw [Fintype.card_fun, Fintype.card_fin]
  congr 1
  simp [Fintype.card_subtype_compl]

/-- 指定座標と基底イデアルの像を含む商は、残る簡約単項式で生成される。 -/
theorem span_coordinateZeroMonomials
    (A : Type u) [CommRing A] {h : ℕ} (t : Fin h → A) (q : ℕ) (hq : 0 < q)
    (i : Fin h) (H : Ideal (MvPolynomial (Fin h) A ⧸ relIdeal A t q))
    (hi : Ideal.Quotient.mk (relIdeal A t q) (X i) ∈ H) :
    Submodule.span A (Set.range fun e : {j : Fin h // j ≠ i} → Fin q =>
      Ideal.Quotient.mk H (redMonomial A t q (coordinateZeroExponent hq i e))) = ⊤ := by
  classical
  let G := Submodule.span A (Set.range fun e : {j : Fin h // j ≠ i} → Fin q =>
    Ideal.Quotient.mk H (redMonomial A t q (coordinateZeroExponent hq i e)))
  have hgen : ∀ e : Fin h → Fin q, Ideal.Quotient.mk H (redMonomial A t q e) ∈ G := by
    intro e
    by_cases he : (e i : ℕ) = 0
    · have hex : coordinateZeroExponent hq i (fun j => e j.1) = e := by
        ext j
        by_cases hj : j = i
        · subst j
          simp [coordinateZeroExponent, he]
        · simp [coordinateZeroExponent, hj]
      rw [← hex]
      exact Submodule.subset_span ⟨_, rfl⟩
    · have hd : (X i : MvPolynomial (Fin h) A) ∣ monomial (expOf q e) 1 :=
        X_dvd_monomial.mpr (Or.inr (by simpa using he))
      have hm : redMonomial A t q e ∈ H := by
        obtain ⟨f, hf⟩ := hd
        rw [redMonomial, hf, map_mul]
        exact H.mul_mem_right _ hi
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hm]
      exact G.zero_mem
  apply top_unique
  intro x hxTop
  clear hxTop
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨f, rfl⟩ := ofRed_surjective A t q hq b
  change Ideal.Quotient.mk H (f.sum fun e a => a • redMonomial A t q e) ∈ G
  rw [map_finsuppSum]
  exact Submodule.sum_mem G fun e _ => by
    change (Ideal.Quotient.mkₐ A H).toLinearMap ((f e) • redMonomial A t q e) ∈ G
    rw [(Ideal.Quotient.mkₐ A H).toLinearMap.map_smul]
    exact G.smul_mem _ (hgen e)

/-- 指定座標を零にした商の A 上の長さは、q^(h-1) 個の A/I の長さ以下。 -/
theorem length_coordinateQuotient_le
    (A : Type u) [CommRing A] {h : ℕ} (t : Fin h → A) (q : ℕ) (hq : 0 < q)
    (I : Ideal A) (i : Fin h)
    (H : Ideal (MvPolynomial (Fin h) A ⧸ relIdeal A t q))
    (hI : I.map (algebraMap A _) ≤ H)
    (hi : Ideal.Quotient.mk (relIdeal A t q) (X i) ∈ H) :
    Module.length A ((MvPolynomial (Fin h) A ⧸ relIdeal A t q) ⧸ H) ≤
      q ^ (h - 1) * Module.length A (A ⧸ I) := by
  have hann : Module.IsTorsionBySet A ((MvPolynomial (Fin h) A ⧸ relIdeal A t q) ⧸ H) I := by
    intro x a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    change a.1 • (Ideal.Quotient.mkₐ A H).toLinearMap b = 0
    rw [← (Ideal.Quotient.mkₐ A H).toLinearMap.map_smul a.1 b]
    rw [Algebra.smul_def]
    change Ideal.Quotient.mk H (algebraMap A _ a.1 * b) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (H.mul_mem_right _
      (hI (Ideal.mem_map_of_mem _ a.2)))
  simpa only [card_coordinateZeroExponent, Nat.cast_pow] using
    length_le_card_mul_quotient_of_span A I _
      (fun e : {j : Fin h // j ≠ i} → Fin q =>
        Ideal.Quotient.mk H (redMonomial A t q (coordinateZeroExponent hq i e)))
      (span_coordinateZeroMonomials A t q hq i H hi) hann

/-- 局所な有限段の通常の長さにも、同じ単項式数の上界が成り立つ。 -/
theorem length_stage_coordinateQuotient_le
    (A : Type u) [CommRing A] [IsLocalRing A] {h : ℕ} (t : Fin h → A)
    (p : ℕ) [Fact p.Prime] (ht : ∀ j, t j ∈ maximalIdeal A) (m : ℕ)
    (I : Ideal A) (i : Fin h) (H : Ideal (TowerStage A t p m))
    (hI : I.map (algebraMap A _) ≤ H) (hi : stageX A t p m i ∈ H) :
    Module.length (TowerStage A t p m) (TowerStage A t p m ⧸ H) ≤
      (p ^ m) ^ (h - 1) * Module.length A (A ⧸ I) := by
  let := isLocalRing_towerStage A t p ht m
  rw [← length_eq_of_common_residueField (residue_surjective_towerStage A t p ht m)]
  exact length_coordinateQuotient_le A t (p ^ m) (pow_pos_of_prime p m) I i H hI hi

/-- 完備塔へ移した座標商の正規化長さは、基底商の長さを p^m で割った値以下。 -/
theorem completedNormalizedLength_tensor_coordinateQuotient_le
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (ht : ∀ j, t j ∈ maximalIdeal A) (hp : (p : A) ∈ maximalIdeal A)
    (m : ℕ) (I : Ideal A) (hfinite : IsFiniteLength A (A ⧸ I))
    (i : Fin h) (H : Ideal (TowerStage A t p m))
    (hI : I.map (algebraMap A _) ≤ H) (hi : stageX A t p m i ∈ H) :
    letI : Module (TowerStage A t p m) (CompletedTower A t p) := Algebra.toModule
    (completedNormalizedLength A t p ht).len
      (CompletedTower A t p ⊗[TowerStage A t p m] (TowerStage A t p m ⧸ H)) ≤
        (Module.length A (A ⧸ I) : ℝ≥0∞) / (p ^ m : ℝ≥0∞) := by
  let : Module (TowerStage A t p m) (CompletedTower A t p) := Algebra.toModule
  have hlen := length_stage_coordinateQuotient_le A t p ht m I i H hI hi
  have htop : ((p ^ m : ℕ∞) ^ (h - 1)) * Module.length A (A ⧸ I) ≠ ⊤ := by
    exact WithTop.mul_ne_top
      (WithTop.pow_ne_top (WithTop.pow_ne_top (ENat.natCast_ne_top p)))
      (Module.length_ne_top_iff.mpr hfinite)
  have hfiniteH : IsFiniteLength (TowerStage A t p m) (TowerStage A t p m ⧸ H) :=
    Module.length_ne_top_iff.mp (ne_top_of_le_ne_top htop hlen)
  rw [completedNormalizedLength_tensor_eq_length A t p ht hp m _ hfiniteH]
  have hc : (Module.length (TowerStage A t p m) (TowerStage A t p m ⧸ H) : ℝ≥0∞) ≤
      (p ^ m : ℝ≥0∞) ^ (h - 1) * (Module.length A (A ⧸ I) : ℝ≥0∞) := by
    exact_mod_cast hlen
  refine (ENNReal.div_le_div_right hc _).trans_eq ?_
  have hh : 1 ≤ h := by have := i.isLt; omega
  have hr : (stageRank h p m : ℝ≥0∞) =
      (p ^ m : ℝ≥0∞) ^ (h - 1) * (p ^ m : ℝ≥0∞) := by
    rw [stageRank, Nat.cast_pow, pow_mul]
    rw [← pow_succ, Nat.sub_add_cancel hh]
  rw [hr]
  exact ENNReal.mul_div_mul_left _ _ (by
    exact pow_ne_zero _ (by exact_mod_cast (pow_pos_of_prime p m).ne')) (by simp)

/-- 有限長の基底商に対し、完備塔の実際の商でも同じ上界を得る。 -/
theorem completedNormalizedLength_coordinateQuotient_le
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (ht : ∀ j, t j ∈ maximalIdeal A) (hp : (p : A) ∈ maximalIdeal A)
    (m : ℕ) (I : Ideal A) (hfinite : IsFiniteLength A (A ⧸ I))
    (i : Fin h) (H : Ideal (TowerStage A t p m))
    (hI : I.map (algebraMap A _) ≤ H) (hi : stageX A t p m i ∈ H) :
    (completedNormalizedLength A t p ht).len
      (CompletedTower A t p ⧸ H.map (algebraMap (TowerStage A t p m) (CompletedTower A t p))) ≤
        (Module.length A (A ⧸ I) : ℝ≥0∞) / (p ^ m : ℝ≥0∞) := by
  let : Module (TowerStage A t p m) (CompletedTower A t p) := Algebra.toModule
  let : SMul (TowerStage A t p m) (CompletedTower A t p) :=
    (inferInstance : Algebra (TowerStage A t p m) (CompletedTower A t p)).toSMul
  rw [(completedNormalizedLength A t p ht).len_congr _ _
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuotAux (CompletedTower A t p) H)]
  exact completedNormalizedLength_tensor_coordinateQuotient_le A t p ht hp m I hfinite i H hI hi

/-- Noether 局所環の極大イデアルの任意の冪による商は有限長。 -/
theorem finiteLength_quotient_maximalIdeal_pow
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (n : ℕ) :
    IsFiniteLength A (A ⧸ (maximalIdeal A) ^ n) := by
  let : IsArtinianRing (A ⧸ maximalIdeal A) :=
    inferInstanceAs (IsArtinianRing (ResidueField A))
  apply isFiniteLength_of_le_radical_annihilator (maximalIdeal A)
  rw [Ideal.annihilator_quotient]
  intro a ha
  exact Ideal.mem_radical_iff.mpr ⟨n, Ideal.pow_mem_pow ha n⟩

/-- 座標根と m_A^n の像で定まる、有限段の具体的なイデアル。 -/
def coordinateQuotientIdeal
    (A : Type u) [CommRing A] [IsLocalRing A] {h : ℕ} (t : Fin h → A)
    (p n m : ℕ) (i : Fin h) : Ideal (TowerStage A t p m) :=
  ((maximalIdeal A) ^ n).map (algebraMap A _) ⊔ Ideal.span {stageX A t p m i}

/-- m_A^n と一つの段座標で切った完備塔商の上界。定数は段 m に依存しない。 -/
theorem completedNormalizedLength_coordinateQuotientIdeal_le
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (ht : ∀ j, t j ∈ maximalIdeal A) (hp : (p : A) ∈ maximalIdeal A)
    (n m : ℕ) (i : Fin h) :
    (completedNormalizedLength A t p ht).len
      (CompletedTower A t p ⧸ (coordinateQuotientIdeal A t p n m i).map
        (algebraMap (TowerStage A t p m) (CompletedTower A t p))) ≤
      (Module.length A (A ⧸ (maximalIdeal A) ^ n) : ℝ≥0∞) / (p ^ m : ℝ≥0∞) := by
  apply completedNormalizedLength_coordinateQuotient_le A t p ht hp m _
    (finiteLength_quotient_maximalIdeal_pow A n) i _ le_sup_left
  exact (le_sup_right : Ideal.span {stageX A t p m i} ≤ _ )
    (Ideal.subset_span (Set.mem_singleton _))

/-- 完備塔のイデアルが m_A^n と指定された段座標を含めば、その商も同じ上界を満たす。 -/
theorem completedNormalizedLength_quotient_le_of_coordinate_mem
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (ht : ∀ j, t j ∈ maximalIdeal A) (hp : (p : A) ∈ maximalIdeal A)
    (n m : ℕ) (i : Fin h) (L : Ideal (CompletedTower A t p))
    (hL : ((maximalIdeal A) ^ n).map (algebraMap A (CompletedTower A t p)) ≤ L)
    (hi : algebraMap (TowerStage A t p m) (CompletedTower A t p) (stageX A t p m i) ∈ L) :
    (completedNormalizedLength A t p ht).len (CompletedTower A t p ⧸ L) ≤
      (Module.length A (A ⧸ (maximalIdeal A) ^ n) : ℝ≥0∞) / (p ^ m : ℝ≥0∞) := by
  let C := CompletedTower A t p
  let H := coordinateQuotientIdeal A t p n m i
  let K := H.map (algebraMap (TowerStage A t p m) C)
  have hbase : ((maximalIdeal A) ^ n).map (algebraMap A C) ≤ K := by
    apply le_of_eq_of_le _ (Ideal.map_mono le_sup_left)
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hKL : K ≤ L := by
    rw [Ideal.map_le_iff_le_comap]
    apply sup_le
    · rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
      exact (Ideal.map_le_iff_le_comap).mp hL
    · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hi)
  let f : (C ⧸ K) →ₗ[C] (C ⧸ L) :=
    (Ideal.quotientMapₐ L (AlgHom.id C C) (by simpa using hKL)).toLinearMap
  have hf : Function.Surjective f := by
    exact Ideal.quotientMap_surjective (H := by simpa using hKL) Function.surjective_id
  have htor : IsPowTorsion (completedTowerMaxIdeal A t p) (C ⧸ K) := by
    refine ⟨n, ?_⟩
    rw [Module.isTorsionBySet_iff_subset_annihilator, SetLike.coe_subset_coe,
      Ideal.annihilator_quotient]
    change (completedTowerMaxIdeal A t p) ^ n ≤ K
    simpa only [completedTowerMaxIdeal, ← Ideal.map_pow] using hbase
  exact ((completedNormalizedLength A t p ht).len_le_of_surjective f hf htor).trans
    (completedNormalizedLength_coordinateQuotientIdeal_le A t p ht hp n m i)

end SerrePositivity.RootTowerLength

end CoordinateQuotientLengthPart

section CoordinateVanishingPart

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

end CoordinateVanishingPart

section CoordinateModuleVanishingPart

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

end CoordinateModuleVanishingPart
