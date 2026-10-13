module

public import SerrePositivity.Paper.Section5.TowerPositivity
public import SerrePositivity.Paper.Section5.Preparation
public import SerrePositivity.Paper.Section2.TowerLengthOn

/-! # 本文のパラメータ商と長さ代数からの正値性

`Z = D′/(ι(x))` と塔の作用 `θ` を構成し、パラメータ系の支持と定理2.5の公式から
`TowerPositivity` の仮定を確認する。商の正の有限な長さは重複度公式から得る。
塔の長さと重複度の正値性は証明済み。新たな未証明入力は置かず、
不変 K₀ 類の降下に関する既存の引用へ依存する。
-/

@[expose] public section

universe u

namespace SerrePositivity.Section5

open CategoryTheory IsLocalRing ParamQuot
open scoped ENNReal

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

/-- (2.5) の一乗の場合から、本文の商 `U = C/(x)C` の長さを計算する。 -/
lemma parameterQuotient_length_eq_multiplicity
    {R D C : Type u} [CommRing R] [CommRing D] [IsLocalRing D]
    [CommRing C] [Algebra D C] (ι : R →+* D) {h : ℕ} (x : Fin h → R)
    (mu : NormalizedLength C ((maximalIdeal D).map (algebraMap D C)))
    (hquot : mu.len (C ⧸ Ideal.span (Set.range fun j ↦ algebraMap D C (ι (x j) ^ 1))) =
      ENNReal.ofReal ((1 : ℝ) ^ h *
        (HilbertSamuel.multiplicity D (Iσ ι x) D : ℝ))) :
    mu.len (U (φσ (C := C) ι) x) =
      ENNReal.ofReal (HilbertSamuel.multiplicity D (Iσ ι x) D : ℝ) := by
  have hspan : Ideal.span (Set.range fun j ↦ algebraMap D C (ι (x j) ^ 1)) =
      IC (φσ (C := C) ι) x := by
    rw [IC_eq]
    simp only [φσ, RingHom.comp_apply, Function.comp_def, pow_one]
  rw [hspan] at hquot
  simpa only [one_pow, one_mul] using hquot

set_option maxHeartbeats 2400000 in
-- 塔と二つの長さ代数の構造を同じパラメータ商に照合する。
/-- 本文のパラメータ商に抽象正値性を適用する。
`D′/(ι(x))`、共通消去冪、台、塔からの写像、商の正の有限な長さを内部で供給する。
入力は二つの有限局所代数、共通剰余体、パラメータ系、長さ代数の公式である。 -/
theorem lambdaChi_pos_of_parameter_lengthAlgebras
    {R D C₀ : Type u} [CommRing R] [IsRegularLocalRing R]
    [CommRing D] [IsLocalRing D] [CommRing C₀] [Algebra D C₀]
    (ι : R →+* D) {h : ℕ} (x : Fin h → R)
    (hx : IsSystemOfParameters D (ι ∘ x))
    (hreg : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn x))
    (hresR : Function.Surjective ((residue D).comp ι))
    (A₀ : Type u) [CommRing A₀] [IsLocalRing A₀] [IsNoetherianRing A₀]
    [Algebra A₀ D] [Module.Finite A₀ D]
    (hinj : Function.Injective (algebraMap A₀ D))
    (hresD : Function.Surjective ((residue D).comp (algebraMap A₀ D)))
    {h₀ : ℕ} (t : Fin h₀ → A₀) (ht : Ideal.span (Set.range t) = maximalIdeal A₀)
    (p₀ : ℕ) [Fact p₀.Prime]
    [Algebra A₀ C₀] [Algebra (Section2.Tower A₀ t p₀) C₀]
    [IsScalarTower A₀ D C₀] [IsScalarTower A₀ (Section2.Tower A₀ t p₀) C₀]
    (hzeroD : ∀ v : ℕ, 0 < v → ∀ q : ℕ, 0 < q →
      (Section2.towerLengthOn A₀ D hinj t p₀
        (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)) C₀).len
        (koszulHomologySelf (fun j ↦ algebraMap D C₀ (ι (x j) ^ v)) q) = 0)
    (hquotD : (Section2.towerLengthOn A₀ D hinj t p₀
        (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)) C₀).len
        (C₀ ⧸ Ideal.span (Set.range fun j ↦ algebraMap D C₀ (ι (x j) ^ 1))) =
      ENNReal.ofReal ((1 : ℝ) ^ h *
        (HilbertSamuel.multiplicity D (Iσ ι x) D : ℝ)))
    (A T C : Type u) [CommRing A] [IsRegularLocalRing A]
    [HasDerivedCategory (ModuleCat.{u} A)]
    [CommRing T] [IsLocalRing T] [IsDomain T] [Algebra A T] [Module.Finite A T]
    [Algebra R T] [Algebra (B x) T] [IsScalarTower R (B x) T] [Module.Finite (B x) T]
    [CommRing C] [Nontrivial C] [Algebra T C]
    (G : Type u) [Group G] [Finite G] [MulSemiringAction G T] [SMulCommClass G A T]
    (lam : NormalizedLength C ((maximalIdeal T).map (algebraMap T C)))
    {e : ℕ} (a : Fin e → A) (ha : Ideal.span (Set.range a) = maximalIdeal A)
    (hdim : ringKrullDim A = e) (hd : ringKrullDim R = (e + h : ℕ))
    (hresA : Function.Surjective ((residue T).comp (algebraMap A T)))
    (hresRT : Function.Surjective ((residue T).comp (algebraMap R T)))
    (hzeroC : ∀ v : ℕ, 0 < v → ∀ i : ℕ, 0 < i → lam.len
      (koszulHomologySelf (fun j ↦ (algebraMap T C (algebraMap A T (a j))) ^ v) i) = 0)
    (hquotC : ∀ v : ℕ, 0 < v → lam.len
      (C ⧸ Ideal.span (Set.range fun j ↦ (algebraMap T C (algebraMap A T (a j))) ^ v)) =
        ((v ^ e * Module.finrank A T : ℕ) : ℝ≥0∞))
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField A) p]
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap A T)))
    (htrans : IsGeometricallyTransitive A T G) :
    0 < lambdaChi (Section2.towerLengthOn A₀ D hinj t p₀
        (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)) C₀) (φσ (C := C₀) ι) T := by
  let mu := Section2.towerLengthOn A₀ D hinj t p₀
        (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)) C₀
  have : IsNoetherianRing D := IsNoetherianRing.of_finite A₀ D
  let := isLocalHom_of_residue_surjective ι hresR
  let := isLocalHom_of_residue_surjective (algebraMap A₀ D) hresD
  have hI : Iσ ι x ≠ ⊤ := by
    intro heq
    have : maximalIdeal D = ⊤ := by rw [← hx.2, show Ideal.span (Set.range (ι ∘ x)) = ⊤
      from heq, Ideal.radical_top]
    exact (maximalIdeal.isMaximal D).ne_top this
  let : Nontrivial (TD ι x) := Ideal.Quotient.nontrivial_iff.mpr hI
  let : IsLocalRing (TD ι x) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (Iσ ι x)) Ideal.Quotient.mk_surjective
  let : Algebra (B x) (TD ι x) := (paramBT ι x).toAlgebra
  let : Nontrivial (B x) := (paramBT ι x).domain_nontrivial
  let : IsLocalRing (B x) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hresBZ : Function.Surjective
      ((residue (TD ι x)).comp (algebraMap (B x) (TD ι x))) := by
    have hs := residue_surjective_comp_of_surjective ι (Ideal.Quotient.mk (Iσ ι x))
      hresR Ideal.Quotient.mk_surjective
    intro z
    obtain ⟨r, hr⟩ := hs z
    exact ⟨Ideal.Quotient.mk _ r, hr⟩
  have hresZ := residue_surjective_comp_of_surjective (algebraMap A₀ D)
    (Ideal.Quotient.mk (Iσ ι x)) hresD Ideal.Quotient.mk_surjective
  have hresBT : Function.Surjective ((residue T).comp (algebraMap (B x) T)) := by
    intro z
    obtain ⟨r, hr⟩ := hresRT z
    refine ⟨algebraMap R (B x) r, ?_⟩
    simpa only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply R (B x) T] using hr
  obtain ⟨v₀, _, hv₀⟩ := exists_pow_maximalIdeal_map_le (algebraMap A₀ D) hx.2.ge
  have hZa : ∀ r ∈ maximalIdeal A₀ ^ v₀, algebraMap A₀ (TD ι x) r = 0 := by
    intro r hr
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hv₀ r hr)
  have hAC : (algebraMap (Section2.Tower A₀ t p₀) C₀).comp
      (algebraMap A₀ (Section2.Tower A₀ t p₀)) =
        (algebraMap D C₀).comp (algebraMap A₀ D) := by
    rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  have hmap : (Iσ ι x).map (algebraMap D C₀) = IC (φσ (C := C₀) ι) x := by
    rw [IC_eq, Iσ, Ideal.map_span, ← Set.range_comp]
    rfl
  have hJrad : (maximalIdeal D).map (algebraMap D C₀) ≤
      (Ideal.span (Set.range (φσ (C := C₀) ι ∘ x))).radical := by
    rw [← hx.2]
    exact (Ideal.map_radical_le (algebraMap D C₀)).trans_eq
      (congrArg Ideal.radical (hmap.trans (IC_eq _ _)))
  have hfg := (maximalIdeal D).fg_of_isNoetherianRing.map (algebraMap D C₀)
  obtain ⟨b, hb⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hJrad hfg
  have hU := parameterQuotient_length_eq_multiplicity ι x mu hquotD
  have hUfin : mu.len (U (φσ (C := C₀) ι) x) ≠ ⊤ := by
    rw [hU]; exact ENNReal.ofReal_ne_top
  have hUpos : 0 < mu.len (U (φσ (C := C₀) ι) x) := by
    rw [hU]
    exact ENNReal.ofReal_pos.mpr (by exact_mod_cast
      HilbertSamuel.multiplicity_pos_of_isSystemOfParameters D (ι ∘ x) hx)
  have hzero : ∀ v : ℕ, 0 < v → ∀ q : ℕ, 0 < q →
      mu.len (koszulHomologySelf (fun j ↦ φσ (C := C₀) ι (x j ^ v)) q) = 0 := by
    intro v hv q hq
    have hw : (fun j ↦ φσ (C := C₀) ι (x j ^ v)) =
        (fun j ↦ algebraMap D C₀ (ι (x j) ^ v)) := by
      ext j
      simp only [φσ, RingHom.comp_apply, map_pow]
    rw [hw]
    exact hzeroD v hv q hq
  exact lambdaChi_pos_of_parameter_tower (φσ (C := C₀) ι) x mu A₀ t p₀
    (fun j ↦ ht ▸ Ideal.subset_span (Set.mem_range_self j)) (TD ι x) hZa hresZ hresBZ
    (Section2.towerMaxIdeal_map_le A₀ D hinj t p₀ C₀) rfl
    (paramTheta ι x A₀ t p₀ hAC) (paramTheta_comp_tower ι x hAC)
    (paramTheta_comp_ψU ι x hAC rfl) hreg hfg (by simpa only [IC_eq] using hb)
    hJrad hzero hUfin hUpos
    A T C G lam a ha hdim hd hresA hresBT hzeroC hquotC p hsurj htrans

end SerrePositivity.Section5
