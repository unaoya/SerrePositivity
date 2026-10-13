module

public import SerrePositivity.Paper.Section5.SelectedParameterPositivity
public import SerrePositivity.Paper.Section2.Theorem2_5
public import SerrePositivity.CommutativeAlgebra.GeometricTransitivity
public import SerrePositivity.LengthAlgebra.Nontrivial
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # 正規化基底と有限群作用から核心の正値性へ

二つの有限局所拡大と正規化基底を受け取り、定理2.5で長さ代数を選ぶ。
共通剰余体から標数・完全性を移し、不変環の条件から幾何的推移性を導く。
パラメータ選択・有限近似・第二比較・第一比較までを接続する。
定理2.5などの既存の引用に依存し、新たな未証明入力は追加しない。
-/

@[expose] public section

universe u

namespace SerrePositivity.Section5

open CategoryTheory IsLocalRing
open scoped ENNReal

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2400000 in
-- 二つの存在定理が返す代数構造を同時に保持して、正値性の入口へ渡す。
/-- 正規化基底と不変環の条件から核心の交点数は正。
長さ代数、その公式、パラメータ、正の階数、幾何的推移性は内部で供給する。
有限拡大・正規化基底・有限群作用の存在構成は、この定理の前段に残る。 -/
theorem core_of_normalization_bases
    {R : Type u} [CommRing R] [IsRegularLocalRing R]
    [PerfectField (ResidueField R)] (p : ℕ) [Fact p.Prime] [CharP (ResidueField R) p]
    (P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    {h e : ℕ} (hh : 0 < h) (he : 0 < e)
    (hPdim : ringKrullDim (R ⧸ P) = h) (hQdim : ringKrullDim (R ⧸ Q) = e)
    (hsum : ringKrullDim (R ⧸ P) + ringKrullDim (R ⧸ Q) = ringKrullDim R)
    (hprimary : (P ⊔ Q).radical = maximalIdeal R)
    (D T : Type u) [CommRing D] [IsLocalRing D] [IsDomain D]
    [IsAdicComplete (maximalIdeal D) D]
    [Algebra R D] [Algebra (R ⧸ P) D] [IsScalarTower R (R ⧸ P) D]
    [Module.Finite (R ⧸ P) D] (hinjPD : Function.Injective (algebraMap (R ⧸ P) D))
    (hresRD : Function.Surjective ((residue D).comp (algebraMap R D)))
    [CommRing T] [IsLocalRing T] [IsDomain T] [IsAdicComplete (maximalIdeal T) T]
    [Algebra R T] [Algebra (R ⧸ Q) T] [IsScalarTower R (R ⧸ Q) T]
    [Module.Finite (R ⧸ Q) T] (hinjQT : Function.Injective (algebraMap (R ⧸ Q) T))
    (hresRT : Function.Surjective ((residue T).comp (algebraMap R T)))
    (A₀ A : Type u) [CommRing A₀] [IsRegularLocalRing A₀]
    [IsAdicComplete (maximalIdeal A₀) A₀]
    [Algebra A₀ D] [Module.Finite A₀ D]
    (hinjD : Function.Injective (algebraMap A₀ D))
    (hsepD : ∀ d : D, ((minpoly A₀ d).map (algebraMap A₀ (FractionRing A₀))).Separable)
    (hresD : Function.Surjective ((residue D).comp (algebraMap A₀ D)))
    (t : Fin h → A₀) (ht : Ideal.span (Set.range t) = maximalIdeal A₀)
    (hdimA₀ : ringKrullDim A₀ = h)
    [CommRing A] [IsRegularLocalRing A] [IsAdicComplete (maximalIdeal A) A]
    [Algebra A T] [Module.Finite A T]
    (hinjT : Function.Injective (algebraMap A T))
    (hsepT : ∀ d : T, ((minpoly A d).map (algebraMap A (FractionRing A))).Separable)
    (hresT : Function.Surjective ((residue T).comp (algebraMap A T)))
    (a : Fin e → A) (ha : Ideal.span (Set.range a) = maximalIdeal A)
    (hdimA : ringKrullDim A = e)
    (G₀ G : Type u) [Group G₀] [Finite G₀] [MulSemiringAction G₀ D]
    [SMulCommClass G₀ A₀ D] [Group G] [Finite G] [MulSemiringAction G T]
    [SMulCommClass G A T]
    (hfixD : ∀ d : D, (∀ g : G₀, g • d = d) → d ∈ Set.range (algebraMap A₀ D))
    (hfixT : ∀ d : T, (∀ g : G, g • d = d) → d ∈ Set.range (algebraMap A T))
    (hbaseD :
      (CharP D p ∧ ∃ f : A₀ ≃+* MvPowerSeries (Fin h) (ResidueField D),
        ∀ i, f (t i) = MvPowerSeries.X i) ∨
      (CharZero D ∧ t ⟨0, hh⟩ = (p : A₀) ∧
        ∃ f : A₀ ≃+* MvPowerSeries {i : Fin h // (i : ℕ) ≠ 0}
          (WittVector p (ResidueField D)),
          ∀ (i : Fin h) (hi : (i : ℕ) ≠ 0), f (t i) = MvPowerSeries.X ⟨i, hi⟩))
    (hbaseT :
      (CharP T p ∧ ∃ f : A ≃+* MvPowerSeries (Fin e) (ResidueField T),
        ∀ i, f (a i) = MvPowerSeries.X i) ∨
      (CharZero T ∧ a ⟨0, he⟩ = (p : A) ∧
        ∃ f : A ≃+* MvPowerSeries {i : Fin e // (i : ℕ) ≠ 0}
          (WittVector p (ResidueField T)),
          ∀ (i : Fin e) (hi : (i : ℕ) ≠ 0), f (a i) = MvPowerSeries.X ⟨i, hi⟩)) :
    0 < chi R (R ⧸ P) (R ⧸ Q) := by
  have : IsNoetherianRing D := IsNoetherianRing.of_finite A₀ D
  have : IsNoetherianRing T := IsNoetherianRing.of_finite A T
  let eD := residueFieldEquiv_of_surjective D hresRD
  let eT := residueFieldEquiv_of_surjective T hresRT
  let eA := residueFieldEquiv_of_surjective T hresT
  have : CharP (ResidueField D) p :=
    charP_of_injective_ringHom (f := eD.toRingHom) eD.injective p
  have : CharP (ResidueField T) p :=
    charP_of_injective_ringHom (f := eT.toRingHom) eT.injective p
  have : CharP (ResidueField A) p :=
    charP_of_injective_ringHom (f := eA.symm.toRingHom) eA.symm.injective p
  have : PerfectField (ResidueField D) := PerfectField.of_ringEquiv eD
  have : PerfectField (ResidueField T) := PerfectField.of_ringEquiv eT
  have htSop : IsSystemOfParameters A₀ t :=
    ⟨hdimA₀, by rw [ht]; exact (maximalIdeal.isMaximal A₀).isPrime.radical⟩
  have haSop : IsSystemOfParameters A a :=
    ⟨hdimA, by rw [ha]; exact (maximalIdeal.isMaximal A).isPrime.radical⟩
  have htD := htSop.map_finite D hinjD
  have haT := haSop.map_finite T hinjT
  obtain ⟨C₀, c₀Ring, a₀Alg, dAlg, t₀Alg, ad₀Tower, at₀Tower, hzeroD, hquotD, _⟩ :=
    Section2.theorem_2_5 A₀ D hinjD hsepD hresD t hdimA₀ htD.1 hh ht htD p hbaseD
  obtain ⟨C, cRing, aAlg, tAlg, towerAlg, atTower, aTower, hzeroT, _, hquotT⟩ :=
    Section2.theorem_2_5 A T hinjT hsepT hresT a hdimA haT.1 he ha haT p hbaseT
  let lam := Section2.towerLengthOn A T hinjT a p
    (fun i ↦ ha ▸ Ideal.subset_span (Set.mem_range_self i)) C
  have : Module.IsTorsionFree (R ⧸ P) D :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinjPD
  have : Module.IsTorsionFree (R ⧸ Q) T :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinjQT
  let : IsDomain A := isDomain_of_isRegularLocalRing A
  have : Module.IsTorsionFree A T := Module.isTorsionFree_iff_algebraMap_injective.mpr hinjT
  have hrank : 0 < Module.finrank A T := Module.finrank_pos
  have hpos : 0 < lam.len
      (C ⧸ Ideal.span (Set.range fun j ↦ algebraMap T C (algebraMap A T (a j) ^ 1))) := by
    rw [hquotT 1 one_pos]
    simpa only [one_pow, one_mul] using
      (show (0 : ℝ≥0∞) < (Module.finrank A T : ℝ≥0∞) by exact_mod_cast hrank)
  have : Nontrivial C := lam.nontrivial_ring_of_len_pos _ hpos
  let : HasDerivedCategory (ModuleCat.{u} A) := HasDerivedCategory.standard _
  have : FaithfulSMul A₀ D := (faithfulSMul_iff_algebraMap_injective A₀ D).mpr hinjD
  have : FaithfulSMul A T := (faithfulSMul_iff_algebraMap_injective A T).mpr hinjT
  have hd : ringKrullDim R = (e + h : ℕ) := by
    rw [← hsum, hPdim, hQdim, Nat.cast_add, add_comm]
  exact core_of_lengthAlgebras_with_parameter_choice P Q G₀ hresRD A₀ hinjD hresD t ht p
    hzeroD hquotD A T C G lam a ha hdimA hd hresT hresRT (hzeroT _ haT) hquotT p
    (Algebra.IsIntegral.comap_surjective A T) (isGeometricallyTransitive_of_fixed hfixT)
    hh hdimA₀ htD (Algebra.IsIntegral.comap_surjective A₀ D)
    (isGeometricallyTransitive_of_fixed hfixD) Module.finrank_pos Module.finrank_pos
    hPdim hQdim hprimary p

end SerrePositivity.Section5
