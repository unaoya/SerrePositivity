module

public import SerrePositivity.CommutativeAlgebra.RootTower.Stage
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.CharP.Reduced
public import SerrePositivity.CommutativeAlgebra.RegularLocalRing.Basic
public import SerrePositivity.CommutativeAlgebra.RegularSequence
public import Mathlib.RingTheory.Ideal.GoingUp
public import SerrePositivity.CommutativeAlgebra.PowerSeries.Expansion
public import SerrePositivity.CommutativeAlgebra.PowerSeries.Basic
public import SerrePositivity.CommutativeAlgebra.Witt.PowerSeries
public import SerrePositivity.CommutativeAlgebra.Length.Basic

/-! # 有限段の p 冪根による商と mod p の比較

## 概要

有限段から mod p への具体的な Frobenius 射（係数 a を a^(p^n)、根の座標 X_i を t_i へ送る）を定義し、p の根による商へ降ろす。根を零にした商が整域ならこの商射は単射で、標準冪級数表示があれば全射である。この比較で、先頭の根を含むイデアルで割った有限段の通常の長さを A/p の像イデアルによる商の通常の長さへ移す。

## 方針

単射性は mod p 商からの整拡大と Frobenius の単射性、全射性は冪級数の剰余分解による。最小パラメータ系の場合は商の整域性も示す。

## 規約

比較の射は基底環 A の作用を Frobenius でねじる環準同型で、A 代数の射ではない。長さの比較でも共通の A 作用に関する線形性は使わない。名前空間は `SerrePositivity.Section2`。

## 使われ方

CLMST の有限段の mod p 像の長さと長さの上界、`RootTower/Perfectoid`。
-/

@[expose] public noncomputable section

universe u

section ModPFrobeniusPart

namespace SerrePositivity.Section2
open MvPolynomial
variable (A : Type u) [CommRing A] {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    [CharP (A ⧸ Ideal.span {(p : A)}) p]

/-- 有限段の多項式表示に対するmod pのFrobenius評価。 -/
def stageModPFrobeniusAux (n : ℕ) : MvPolynomial (Fin h) A →+* A ⧸ Ideal.span {(p : A)} :=
  eval₂Hom ((iterateFrobenius (A ⧸ Ideal.span {(p : A)}) p n).comp
    (Ideal.Quotient.mk (Ideal.span {(p : A)})))
    (fun i ↦ Ideal.Quotient.mk (Ideal.span {(p : A)}) (t i))

/-- X_i^(p^n)-t_iはmod pのFrobenius評価で零になる。 -/
theorem towerRel_le_ker_stageModPFrobeniusAux (n : ℕ) :
    towerRel A t p n ≤ RingHom.ker (stageModPFrobeniusAux A t p n) := by
  change Ideal.span (Set.range (fun i ↦ (X i : MvPolynomial (Fin h) A) ^ (p ^ n) - C (t i))) ≤ _
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  change stageModPFrobeniusAux A t p n ((X i) ^ (p ^ n) - C (t i)) = 0
  simp only [stageModPFrobeniusAux, map_sub, map_pow, eval₂Hom_X', eval₂Hom_C,
    RingHom.comp_apply, iterateFrobenius_def, sub_self]

/-- 有限段の環からA/pへの実際の射。 -/
def stageModPFrobenius (n : ℕ) : TowerStage A t p n →+* A ⧸ Ideal.span {(p : A)} :=
  Ideal.Quotient.lift (towerRel A t p n) (stageModPFrobeniusAux A t p n)
    (towerRel_le_ker_stageModPFrobeniusAux A t p n)

@[simp] theorem stageModPFrobenius_stageX (n : ℕ) (i : Fin h) :
    stageModPFrobenius A t p n (stageX A t p n i) =
      Ideal.Quotient.mk (Ideal.span {(p : A)}) (t i) := by
  exact eval₂Hom_X' _ _ _

@[simp] theorem stageModPFrobenius_algebraMap (n : ℕ) (a : A) :
    stageModPFrobenius A t p n (algebraMap A (TowerStage A t p n) a) =
      Ideal.Quotient.mk (Ideal.span {(p : A)}) a ^ (p ^ n) := by
  change stageModPFrobeniusAux A t p n (C a) = _
  exact eval₂Hom_C _ _ _

/-- 先頭として選んだ座標がpなら、そのp冪根の生成イデアルは射の核に入る。 -/
theorem span_stageRoot_le_ker_modPFrobenius (n : ℕ) (i : Fin h) (hti : t i = (p : A)) :
    Ideal.span {stageX A t p n i} ≤ RingHom.ker (stageModPFrobenius A t p n) := by
  rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, stageModPFrobenius_stageX, hti]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

/-- pの根を零にした有限段の商からA/pへのFrobenius射。 -/
def stageRootModPFrobenius (n : ℕ) (i : Fin h) (hti : t i = (p : A)) :
    TowerStage A t p n ⧸ Ideal.span {stageX A t p n i} →+* A ⧸ Ideal.span {(p : A)} :=
  Ideal.Quotient.lift _ (stageModPFrobenius A t p n)
    (span_stageRoot_le_ker_modPFrobenius A t p n i hti)

@[simp] theorem stageRootModPFrobenius_mk (n : ℕ) (i : Fin h) (hti : t i = (p : A))
    (z : TowerStage A t p n) :
    stageRootModPFrobenius A t p n i hti (Ideal.Quotient.mk _ z) =
      stageModPFrobenius A t p n z := rfl

/-- 単射な商射が構成できれば、元の射の核はpの根の生成イデアルに一致する。 -/
theorem stageModPFrobenius_ker_of_quotient_injective
    (n : ℕ) (i : Fin h) (hti : t i = (p : A))
    (hf : Function.Injective (stageRootModPFrobenius A t p n i hti)) :
    RingHom.ker (stageModPFrobenius A t p n) = Ideal.span {stageX A t p n i} := by
  have heq : stageModPFrobenius A t p n =
      (stageRootModPFrobenius A t p n i hti).comp
        (Ideal.Quotient.mk (Ideal.span {stageX A t p n i})) := rfl
  rw [heq, RingHom.ker_comp_of_injective _ hf, Ideal.mk_ker]

/-- 有限段の射は、基底環からの作用をmod pの反復Frobeniusへ送る。 -/
theorem stageModPFrobenius_comp_algebraMap (n : ℕ) :
    (stageModPFrobenius A t p n).comp (algebraMap A (TowerStage A t p n)) =
      (iterateFrobenius (A ⧸ Ideal.span {(p : A)}) p n).comp
        (Ideal.Quotient.mk (Ideal.span {(p : A)})) := by
  ext a
  exact stageModPFrobenius_algebraMap A t p n a

/-- n乗根をm段で取ったとき、m段のFrobenius射による像はg^(p^(m-n))となる。
段と根の指数の差を、実際の像の冪として追跡する。 -/
theorem stageModPFrobenius_root_image [IsReduced (A ⧸ Ideal.span {(p : A)})]
    (n m : ℕ) (hnm : n ≤ m) (g : A) (z : TowerStage A t p m)
    (hz : z ^ (p ^ n) - algebraMap A (TowerStage A t p m) g ∈
      Ideal.span {(p : TowerStage A t p m)}) :
    stageModPFrobenius A t p m z =
      Ideal.Quotient.mk (Ideal.span {(p : A)}) g ^ (p ^ (m - n)) := by
  have hmap := Ideal.mem_map_of_mem (stageModPFrobenius A t p m) hz
  simp only [Ideal.map_span, Set.image_singleton, map_natCast, CharP.cast_eq_zero,
    Ideal.span_singleton_zero, Ideal.mem_bot, map_sub, map_pow,
    stageModPFrobenius_algebraMap] at hmap
  apply iterateFrobenius_inj (A ⧸ Ideal.span {(p : A)}) p n
  change stageModPFrobenius A t p m z ^ (p ^ n) =
    (Ideal.Quotient.mk (Ideal.span {(p : A)}) g ^ (p ^ (m - n))) ^ (p ^ n)
  rw [sub_eq_zero.mp hmap, ← pow_mul, ← pow_add, Nat.sub_add_cancel hnm]

/-- 基底極大イデアルの有限段への拡大は、mod p射によってFrobenius冪イデアルへ送られる。 -/
theorem stageModPFrobenius_map_base_maximalIdeal
    [IsLocalRing A] [IsLocalRing (A ⧸ Ideal.span {(p : A)})] (m : ℕ) :
    ((IsLocalRing.maximalIdeal A).map (algebraMap A (TowerStage A t p m))).map
      (stageModPFrobenius A t p m) =
        (IsLocalRing.maximalIdeal (A ⧸ Ideal.span {(p : A)})).map
          (iterateFrobenius (A ⧸ Ideal.span {(p : A)}) p m) := by
  rw [Ideal.map_map, stageModPFrobenius_comp_algebraMap, ← Ideal.map_map,
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective]

/-- 根を零にし、根の代表元zを加えた有限段の関係式の、mod p射による実際の像。 -/
theorem stageModPFrobenius_map_root_relations
    [IsLocalRing A] [IsLocalRing (A ⧸ Ideal.span {(p : A)})]
    [IsReduced (A ⧸ Ideal.span {(p : A)})]
    (n m : ℕ) (hnm : n ≤ m) (i : Fin h) (hti : t i = (p : A))
    (g : A) (z : TowerStage A t p m)
    (hz : z ^ (p ^ n) - algebraMap A (TowerStage A t p m) g ∈
      Ideal.span {(p : TowerStage A t p m)}) :
    ((IsLocalRing.maximalIdeal A).map (algebraMap A (TowerStage A t p m)) ⊔
      Ideal.span {stageX A t p m i} ⊔ Ideal.span {z}).map (stageModPFrobenius A t p m) =
        (IsLocalRing.maximalIdeal (A ⧸ Ideal.span {(p : A)})).map
          (iterateFrobenius (A ⧸ Ideal.span {(p : A)}) p m) ⊔
            Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : A)}) g ^ (p ^ (m - n))} := by
  rw [Ideal.map_sup, Ideal.map_sup, stageModPFrobenius_map_base_maximalIdeal,
    Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton,
    stageModPFrobenius_stageX, hti]
  have hp : Ideal.Quotient.mk (Ideal.span {(p : A)}) (p : A) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  rw [hp, Ideal.span_singleton_zero, sup_bot_eq,
    stageModPFrobenius_root_image A t p n m hnm g z hz]

/-- n段のp冪根をm段の冪として加えた関係式も、同じFrobenius商の関係式へ送られる。
源での冪の倍率は別のフィルトレーションで評価する。 -/
theorem stageModPFrobenius_map_root_power_relations
    [IsLocalRing A] [IsLocalRing (A ⧸ Ideal.span {(p : A)})]
    [IsReduced (A ⧸ Ideal.span {(p : A)})]
    (n m : ℕ) (hnm : n ≤ m) (i : Fin h) (hti : t i = (p : A))
    (g : A) (z : TowerStage A t p m)
    (hz : z ^ (p ^ n) - algebraMap A (TowerStage A t p m) g ∈
      Ideal.span {(p : TowerStage A t p m)}) :
    ((IsLocalRing.maximalIdeal A).map (algebraMap A (TowerStage A t p m)) ⊔
      Ideal.span {stageX A t p m i ^ (p ^ (m - n))} ⊔ Ideal.span {z}).map
        (stageModPFrobenius A t p m) =
          (IsLocalRing.maximalIdeal (A ⧸ Ideal.span {(p : A)})).map
            (iterateFrobenius (A ⧸ Ideal.span {(p : A)}) p m) ⊔
              Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : A)}) g ^ (p ^ (m - n))} := by
  rw [Ideal.map_sup, Ideal.map_sup, stageModPFrobenius_map_base_maximalIdeal,
    Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, map_pow,
    stageModPFrobenius_stageX, hti]
  have hp : Ideal.Quotient.mk (Ideal.span {(p : A)}) (p : A) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  rw [hp, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero),
    Ideal.span_singleton_zero, sup_bot_eq, stageModPFrobenius_root_image A t p n m hnm g z hz]

end SerrePositivity.Section2

end ModPFrobeniusPart

section ModPInjectivityPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.Section2
open IsLocalRing
variable (A : Type*) [CommRing A] {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]

/-- pは、そのp冪根が生成するイデアルの逆像に入る。 -/
theorem span_p_le_comap_stageRoot (n : ℕ) (j : Fin h) (htj : t j = (p : A)) :
    Ideal.span {(p : A)} ≤
      (Ideal.span {stageX A t p n j}).comap (algebraMap A (TowerStage A t p n)) := by
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, ← htj, ← mk_X_pow A t p n j]
  exact Ideal.pow_mem_of_mem _ (Ideal.subset_span (Set.mem_singleton _)) _
    (pow_pos (Fact.out : p.Prime).pos n)

/-- 商環が整域なら、有限段からのFrobenius商射は単射。
冪級数表示や全射性には依存しない。 -/
theorem stageRootModPFrobenius_injective_of_isDomain
    [CharP (A ⧸ Ideal.span {(p : A)}) p]
    [IsDomain (A ⧸ Ideal.span {(p : A)})]
    (n : ℕ) (j : Fin h) (htj : t j = (p : A))
    [IsDomain (TowerStage A t p n ⧸ Ideal.span {stageX A t p n j})] :
    Function.Injective (stageRootModPFrobenius A t p n j htj) := by
  let Q := A ⧸ Ideal.span {(p : A)}
  let B := TowerStage A t p n ⧸ Ideal.span {stageX A t p n j}
  let : Algebra Q B := Ideal.Quotient.algebraQuotientOfLEComap
    (span_p_le_comap_stageRoot A t p n j htj)
  let : IsScalarTower A Q B := IsScalarTower.of_algebraMap_eq' rfl
  let := isIntegral_towerStage A t p n
  let : Algebra.IsIntegral A B := Algebra.IsIntegral.of_surjective
    (Ideal.Quotient.mkₐ A _) Ideal.Quotient.mk_surjective
  let : Algebra.IsIntegral Q B := ⟨fun b ↦ (Algebra.IsIntegral.isIntegral (R := A) b).tower_top⟩
  let f := stageRootModPFrobenius A t p n j htj
  have hcomp : f.comp (algebraMap Q B) = iterateFrobenius Q p n := by
    ext a
    exact stageModPFrobenius_algebraMap A t p n a
  apply (RingHom.injective_iff_ker_eq_bot f).mpr
  apply Ideal.eq_bot_of_under_eq_bot (R := Q)
  change Ideal.comap (algebraMap Q B) (RingHom.ker f) = ⊥
  rw [RingHom.comap_ker, hcomp]
  exact (RingHom.injective_iff_ker_eq_bot (iterateFrobenius Q p n)).mp
    (iterateFrobenius_inj Q p n)

/-- 最小パラメータ系の先頭の根を零にした有限段の商は整域。 -/
theorem stageRootQuotient_isDomain_of_parameters [IsLocalRing A] [IsNoetherianRing A]
    {r : ℕ} (t : Fin (r + 1) → A)
    (ht : Ideal.span (Set.range t) = maximalIdeal A)
    (hdim : ringKrullDim A = r + 1) (n : ℕ) :
    IsDomain (TowerStage A t p n ⧸ Ideal.span {stageX A t p n 0}) := by
  have htmem : ∀ i, t i ∈ maximalIdeal A := fun i ↦
    ht ▸ Ideal.subset_span (Set.mem_range_self i)
  let := isLocalRing_towerStage A t p htmem n
  let := towerStage_finite A t p n
  let := towerStage_free A t p n
  let := isIntegral_towerStage A t p n
  let : IsNoetherianRing (TowerStage A t p n) := IsNoetherianRing.of_finite A _
  have hdimn : ringKrullDim (TowerStage A t p n) = r + 1 :=
    (ringKrullDim_eq_of_integral_of_injective A _
      (FaithfulSMul.algebraMap_injective A _)).trans hdim
  have hgen := span_stageX_eq_maximalIdeal A t p htmem ht n
  let : IsRegularLocalRing (TowerStage A t p n ⧸ Ideal.span {stageX A t p n 0}) :=
    (isRegularLocalRing_quotient_head_and_dim
      (stageX A t p n) hgen hdimn).1
  obtain ⟨rs, hreg, hspan, _⟩ := exists_regular_generators
    (TowerStage A t p n ⧸ Ideal.span {stageX A t p n 0})
  exact isDomain_of_regular_generators rs hreg hspan

end SerrePositivity.Section2

end ModPInjectivityPart

section ModPSurjectivityPart

namespace SerrePositivity.Section2
variable {A k σ : Type*} [CommRing A] [CommRing k] [Finite σ]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    [CharP k p] [PerfectRing k p] [CharP (A ⧸ Ideal.span {(p : A)}) p]

/-- mod p の座標冪級数表示があれば、有限段 Frobenius 射は全射。 -/
theorem stageModPFrobenius_surjective_of_powerSeries
    (e : A ⧸ Ideal.span {(p : A)} ≃+* MvPowerSeries σ k)
    (ι : σ → Fin h)
    (ht : ∀ i, e (Ideal.Quotient.mk (Ideal.span {(p : A)}) (t (ι i))) = MvPowerSeries.X i)
    (n : ℕ) : Function.Surjective (stageModPFrobenius A t p n) := by
  let f := e.toRingHom.comp (stageModPFrobenius A t p n)
  have hf : Function.Surjective f := by
    apply powerSeries_surjective_of_powers_and_variables p n
    · intro φ
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (e.symm φ)
      refine ⟨algebraMap A (TowerStage A t p n) a, ?_⟩
      change e (stageModPFrobenius A t p n (algebraMap A (TowerStage A t p n) a)) = _
      rw [stageModPFrobenius_algebraMap, map_pow, ha, e.apply_symm_apply]
    · intro i
      refine ⟨stageX A t p n (ι i), ?_⟩
      change e (stageModPFrobenius A t p n (stageX A t p n (ι i))) = _
      rw [stageModPFrobenius_stageX, ht]
  intro a
  obtain ⟨b, hb⟩ := hf (e a)
  exact ⟨b, e.injective hb⟩

/-- pの根を零にした商射も全射である。単射性は別途必要。 -/
theorem stageRootModPFrobenius_surjective_of_powerSeries
    (e : A ⧸ Ideal.span {(p : A)} ≃+* MvPowerSeries σ k)
    (ι : σ → Fin h)
    (ht : ∀ i, e (Ideal.Quotient.mk (Ideal.span {(p : A)}) (t (ι i))) = MvPowerSeries.X i)
    (n : ℕ) (j : Fin h) (htj : t j = (p : A)) :
    Function.Surjective (stageRootModPFrobenius A t p n j htj) := by
  intro a
  obtain ⟨b, hb⟩ := stageModPFrobenius_surjective_of_powerSeries t p e ι ht n a
  exact ⟨Ideal.Quotient.mk _ b, hb⟩

end SerrePositivity.Section2

end ModPSurjectivityPart

section ModPEquivPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.Section2
open IsLocalRing
variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {r : ℕ} (t : Fin (r + 1) → A) (p : ℕ) [Fact p.Prime]
    [CharP (A ⧸ Ideal.span {(p : A)}) p]

/-- 最小パラメータ系とmod pの冪級数表示から、実際のFrobenius商射は全単射。 -/
theorem stageRootModPFrobenius_bijective_of_powerSeries
    {k σ : Type*} [CommRing k] [Finite σ] [CharP k p] [PerfectRing k p]
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (htp : t 0 = (p : A))
    (hdim : ringKrullDim A = r + 1)
    (e : A ⧸ Ideal.span {(p : A)} ≃+* MvPowerSeries σ k) (ι : σ → Fin (r + 1))
    (he : ∀ i, e (Ideal.Quotient.mk (Ideal.span {(p : A)}) (t (ι i))) = MvPowerSeries.X i)
    (n : ℕ) : Function.Bijective (stageRootModPFrobenius A t p n 0 htp) := by
  let : IsDomain (TowerStage A t p n ⧸ Ideal.span {stageX A t p n 0}) :=
    stageRootQuotient_isDomain_of_parameters A p t ht hdim n
  have hQ := isRegularLocalRing_quotient_head_and_dim t ht hdim
  rw [htp] at hQ
  let : IsRegularLocalRing (A ⧸ Ideal.span {(p : A)}) := hQ.1
  obtain ⟨rs, hreg, hgen, _⟩ := exists_regular_generators (A ⧸ Ideal.span {(p : A)})
  let : IsDomain (A ⧸ Ideal.span {(p : A)}) := isDomain_of_regular_generators rs hreg hgen
  exact ⟨stageRootModPFrobenius_injective_of_isDomain A t p n 0 htp,
    stageRootModPFrobenius_surjective_of_powerSeries t p e ι he n 0 htp⟩

end SerrePositivity.Section2

end ModPEquivPart

section ModPComparisonLengthPart

namespace SerrePositivity.Section2
open IsLocalRing
variable (A : Type*) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {r : ℕ} (t : Fin (r + 1) → A) (p : ℕ) [Fact p.Prime]
    [CharP (A ⧸ Ideal.span {(p : A)}) p]

/-- 実際のFrobenius射により、根を含む任意の商の長さが像の商の長さに一致する。 -/
theorem length_stage_quotient_eq_modP_image
    {k σ : Type*} [CommRing k] [Finite σ] [CharP k p] [PerfectRing k p]
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (htp : t 0 = (p : A))
    (hdim : ringKrullDim A = r + 1)
    (e : A ⧸ Ideal.span {(p : A)} ≃+* MvPowerSeries σ k) (ι : σ → Fin (r + 1))
    (he : ∀ i, e (Ideal.Quotient.mk (Ideal.span {(p : A)}) (t (ι i))) = MvPowerSeries.X i)
    (n : ℕ) (I : Ideal (TowerStage A t p n))
    (hI : Ideal.span {stageX A t p n 0} ≤ I) :
    Module.length (TowerStage A t p n) (TowerStage A t p n ⧸ I) =
      Module.length (A ⧸ Ideal.span {(p : A)})
        ((A ⧸ Ideal.span {(p : A)}) ⧸ I.map (stageModPFrobenius A t p n)) := by
  have hf := stageRootModPFrobenius_bijective_of_powerSeries A t p ht htp hdim e ι he n
  apply length_quotient_eq_image_of_surjective _
    (stageModPFrobenius_surjective_of_powerSeries t p e ι he n)
  rw [stageModPFrobenius_ker_of_quotient_injective A t p n 0 htp hf.1]
  exact hI

end SerrePositivity.Section2

end ModPComparisonLengthPart
