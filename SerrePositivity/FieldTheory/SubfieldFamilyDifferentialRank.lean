module

public import SerrePositivity.FieldTheory.PowerSubfieldFamilyIntersection
public import SerrePositivity.FieldTheory.ExponentOneDifferentialConstants
public import SerrePositivity.FieldTheory.PrimeRootDifferentialRank
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.TensorProduct.Finite

/-! # 共有限な部分体族と Kähler 微分の階数の安定

概要：交わりが `K^p` の共有限な部分体族について、十分小さい共通の底体 `R` の上で、有限拡大 `L/K` の後も
`dim Ω_{L/R} = dim Ω_{K/R}`（`exists_subfieldFamily_rank_stable`）。
方針：p 乗根一段は、関係式の微分が族の一つの体の上で零でないことから次元の等式を得る。
有限拡大は、交わりの定理（`PowerSubfieldFamilyIntersection`）と同じく、純非分離な段の帰納と分離閉包で組み立てる。
使われ方：共有限な中間係数体上の微分の階数（CommutativeAlgebra の Cofinite 系）。
-/

@[expose] public noncomputable section
namespace SerrePositivity

section PrimeRootStep

variable {K L ι : Type*} [Field K] [Field L] [Algebra K L]
  {p : ℕ} [Fact p.Prime] [CharP K p] [CharP L p]

/-- p乗でない指定元は、交わりK^pを持つ共有限族の一つの体上で微分が非零。 -/
theorem exists_subfieldFamily_kaehlerDifferential_ne_zero
    (E : ι → Subfield K) (hfin : ∀ i, Module.Finite (E i) K)
    (hpowE : ∀ i, pPowerSubfield K p ≤ E i) (hinf : (⨅ i, E i) = pPowerSubfield K p)
    (a : K) (ha : a ∉ pPowerSubfield K p) :
    ∃ i : ι, KaehlerDifferential.D (E i) K a ≠ 0 := by
  classical
  have hex : ∃ i, a ∉ E i := by
    by_contra h
    apply ha
    rw [← hinf]
    exact Subfield.mem_iInf.mpr (by simpa only [not_exists, not_not] using h)
  obtain ⟨i, hi⟩ := hex
  let : Module.Finite (E i) K := hfin i
  exact ⟨i, fun h ↦ hi ((kaehlerDifferential_finite_subfield_eq_zero_iff (E i) (hpowE i) a).mp h)⟩

/-- 係数作用を保った同じ底体Rについて、像の包含から次数pの次元等号を得る。
RをKの部分体そのものとして表すことは要求しない。 -/
theorem exists_subfieldFamily_primeRoot_rank_stable_of_range
    (E : ι → Subfield K) (hfin : ∀ i, Module.Finite (E i) K)
    (hpowE : ∀ i, pPowerSubfield K p ≤ E i) (hinf : (⨅ i, E i) = pPowerSubfield K p)
    (x : L) (a : K) (hpow : x ^ p = algebraMap K L a)
    (hx : x ∉ Set.range (algebraMap K L)) (hs : Algebra.adjoin K {x} = ⊤) :
    ∃ i : ι, ∀ (R : Type*) [Field R] [Algebra R K] [Algebra R L]
      [IsScalarTower R K L] [Module.Finite R K],
      Set.range (algebraMap R K) ⊆ E i →
      Module.finrank L (KaehlerDifferential R L) = Module.finrank K (KaehlerDifferential R K) := by
  have ha : a ∉ pPowerSubfield K p := by
    intro h
    obtain ⟨c, hc⟩ := (mem_pPowerSubfield K p a).mp h
    exact primeRoot_coefficient_not_pow x a hpow hx c hc
  obtain ⟨i, hi⟩ := exists_subfieldFamily_kaehlerDifferential_ne_zero E hfin hpowE hinf a ha
  refine ⟨i, ?_⟩
  intro R _ _ _ _ _ hR
  let f : R →+* E i := (algebraMap R K).codRestrict (E i) (fun r ↦ hR ⟨r, rfl⟩)
  let : Algebra R (E i) := f.toAlgebra
  let : IsScalarTower R (E i) K := IsScalarTower.of_algebraMap_eq' rfl
  exact finrank_kaehlerDifferential_primeRoot_tower_eq_of_baseRestriction R (E i) x a hpow hx hs hi

/-- 交わりがp乗部分体となる共有限な族では、次数pの添加の微分の次元が十分小さい底体で安定する。 -/
theorem exists_subfieldFamily_primeRoot_rank_stable
    (E : ι → Subfield K) (hfin : ∀ i, Module.Finite (E i) K)
    (hpowE : ∀ i, pPowerSubfield K p ≤ E i) (hinf : (⨅ i, E i) = pPowerSubfield K p)
    (x : L) (a : K) (hpow : x ^ p = algebraMap K L a)
    (hx : x ∉ Set.range (algebraMap K L)) (hs : Algebra.adjoin K {x} = ⊤) :
    ∃ i : ι, ∀ R : Subfield K, Module.Finite R K → R ≤ E i →
      letI : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
      letI : Module R L := @Algebra.toModule _ _ _ _ (inferInstance : Algebra R L)
      letI : SMul R L := (inferInstance : Algebra R L).toSMul
      Module.finrank L (KaehlerDifferential R L) = Module.finrank K (KaehlerDifferential R K) := by
  obtain ⟨i, hi⟩ := exists_subfieldFamily_primeRoot_rank_stable_of_range
    E hfin hpowE hinf x a hpow hx hs
  refine ⟨i, ?_⟩
  intro R hRfin hR
  let : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  let : Module R L := @Algebra.toModule _ _ _ _ (inferInstance : Algebra R L)
  let : SMul R L := (inferInstance : Algebra R L).toSMul
  let : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq' (R := R) (S := K) (A := L) rfl
  let : Module.Finite R K := hRfin
  exact hi R (by rintro _ ⟨r, rfl⟩; exact hR r.property)

end PrimeRootStep

section FiniteExtension

universe u v w t

/-- 塔 `R → K → T → L` での次元の等式の合成。`R` の `T` への作用を `R → K → T` の合成で入れ、
`Ω_{L/R}` と `Ω_{T/R}`、`Ω_{T/R}` と `Ω_{K/R}` の二つの等式をつなぐ。 -/
theorem finrank_kaehlerDifferential_eq_of_tower {R K T L : Type*} [Field R] [Field K] [Field T]
    [Field L] [Algebra R K] [Algebra R L] [Algebra K T] [Algebra T L] [Algebra K L]
    [IsScalarTower R K L] [IsScalarTower K T L] [Module.Finite R K] [Module.Finite K T]
    (hTL : ∀ [Algebra R T] [IsScalarTower R K T] [IsScalarTower R T L] [Module.Finite R T],
      Module.finrank L (KaehlerDifferential R L) = Module.finrank T (KaehlerDifferential R T))
    (hKT : ∀ [Algebra R T] [IsScalarTower R K T],
      Module.finrank T (KaehlerDifferential R T) = Module.finrank K (KaehlerDifferential R K)) :
    Module.finrank L (KaehlerDifferential R L) = Module.finrank K (KaehlerDifferential R K) := by
  let : Algebra R T := ((algebraMap K T).comp (algebraMap R K)).toAlgebra
  let : IsScalarTower R K T := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R T L := IsScalarTower.of_algebraMap_eq' (by
    change algebraMap R L = (algebraMap T L).comp ((algebraMap K T).comp (algebraMap R K))
    rw [← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq])
  let : Module.Finite R T := Module.Finite.trans (R := R) K T
  exact hTL.trans hKT

/-- 形式的エタールな `T/K` では `dim Ω_{T/R} = dim Ω_{K/R}`。 -/
theorem finrank_kaehlerDifferential_of_formallyEtale {R K T : Type*} [Field R] [Field K] [Field T]
    [Algebra R K] [Algebra K T] [Algebra R T] [IsScalarTower R K T] [Algebra.FormallyEtale K T] :
    Module.finrank T (KaehlerDifferential R T) = Module.finrank K (KaehlerDifferential R K) := by
  rw [← (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R K T).finrank_eq,
    Module.finrank_baseChange]

private theorem exists_rank_stable_purelyInseparable_sameUniverse
    (L : Type v) [Field L] (p : ℕ) [Fact p.Prime] [CharP L p]
    {ι : Type t} [Nonempty ι] :
    ∀ (K : Type v) [Field K] [Algebra K L] [CharP K p]
      [IsPurelyInseparable K L] [Module.Finite K L],
      ∀ (E : ι → Subfield K), (∀ i, Module.Finite (E i) K) →
        Directed (· ≥ ·) E →
        (∀ i, pPowerSubfield K p ≤ E i) →
        (⨅ i, E i) = pPowerSubfield K p →
        ∃ i, ∀ (R : Type w) [Field R] [Algebra R K] [Algebra R L]
          [IsScalarTower R K L] [Module.Finite R K],
          Set.range (algebraMap R K) ⊆ E i →
          Module.finrank L (KaehlerDifferential R L) =
            Module.finrank K (KaehlerDifferential R K) := by
  intro K _ _ _ _ _
  refine induction_on_primeRoot_of_isPurelyInseparable (p := p)
    (P := fun K [Field K] [Algebra K L] ↦ ∀ [CharP K p] (E : ι → Subfield K),
      (∀ i, Module.Finite (E i) K) → Directed (· ≥ ·) E → (∀ i, pPowerSubfield K p ≤ E i) →
      (⨅ i, E i) = pPowerSubfield K p →
      ∃ i, ∀ (R : Type w) [Field R] [Algebra R K] [Algebra R L]
        [IsScalarTower R K L] [Module.Finite R K],
        Set.range (algebraMap R K) ⊆ E i →
        Module.finrank L (KaehlerDifferential R L) =
          Module.finrank K (KaehlerDifferential R K)) ?_ ?_ K
  · intro K _ _ hsurj _ E _ _ _ _
    let : Algebra.IsSeparable K L := ⟨fun x ↦ by
      obtain ⟨c, rfl⟩ := hsurj x
      exact isSeparable_algebraMap (F := K) c⟩
    have := Algebra.FormallyEtale.of_isSeparable K L
    exact ⟨Classical.arbitrary ι, fun R _ _ _ _ _ _ ↦ finrank_kaehlerDifferential_of_formallyEtale⟩
  · intro K _ _ _ _ _ x a hxp hx IH _ E hfin hdir hpow hinf
    let T := IntermediateField.adjoin K {x}
    let : CharP T p := (algebraMap T L).charP (algebraMap T L).injective p
    obtain ⟨hpT, hxT, hsT⟩ := primeRoot_adjoin_gen_properties x a hxp hx
    obtain ⟨j, hj⟩ := exists_subfieldFamily_primeRoot_rank_stable_of_range E hfin hpow hinf
      _ a hpT hxT hsT
    let G := fun i ↦ (E i).map (algebraMap K T) ⊔ pPowerSubfield T p
    have hfinG (i) : Module.Finite (G i) T := by
      let : Module.Finite (E i) K := hfin i
      exact finite_subfield_sup_pPower (E i)
    obtain ⟨i, hi⟩ := IH G hfinG (directed_subfield_sup_pPower E hdir) (fun _ ↦ le_sup_right)
      (iInf_subfield_sup_pPower_primeRoot E hdir hpow hinf _ a hpT hxT hsT)
    obtain ⟨k, hki, hkj⟩ := hdir i j
    refine ⟨k, fun R _ _ _ _ _ hR ↦ finrank_kaehlerDifferential_eq_of_tower (T := T)
      (hi R fun _ ⟨r, hr⟩ ↦ hr ▸ (show (E i).map (algebraMap K T) ≤ G i from le_sup_left)
        (Subfield.mem_map.mpr ⟨algebraMap R K r, hki (hR ⟨r, rfl⟩),
          (IsScalarTower.algebraMap_apply R K T r).symm⟩))
      (hj R fun _ hr ↦ hkj (hR hr))⟩

/-- 有限純非分離拡大での階数安定。同じ底体と同じ指定済みの作用で比較する。 -/
theorem exists_subfieldFamily_rank_stable_of_isPurelyInseparable
    {K : Type u} {L : Type v} {ι : Type t} [Field K] [Field L] [Algebra K L]
    {p : ℕ} [Fact p.Prime] [CharP K p] [CharP L p]
    [Module.Finite K L] [IsPurelyInseparable K L] [Nonempty ι]
    (E : ι → Subfield K) (hfin : ∀ i, Module.Finite (E i) K)
    (hdir : Directed (· ≥ ·) E)
    (hpow : ∀ i, pPowerSubfield K p ≤ E i)
    (hinf : (⨅ i, E i) = pPowerSubfield K p) :
    ∃ i, ∀ (R : Type w) [Field R] [Algebra R K] [Algebra R L]
      [IsScalarTower R K L] [Module.Finite R K],
      Set.range (algebraMap R K) ⊆ E i →
      Module.finrank L (KaehlerDifferential R L) = Module.finrank K (KaehlerDifferential R K) := by
  let T : IntermediateField K L := ⊥
  let : CharP T p := (algebraMap T L).charP (algebraMap T L).injective p
  let : IsPurelyInseparable T L := IsPurelyInseparable.tower_top K T L
  let G := fun i ↦ (E i).map (algebraMap K T)
  have hsurj : Function.Surjective (algebraMap K T) := by
    intro t
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp t.property
    exact ⟨c, Subtype.ext hc⟩
  let : Algebra.IsSeparable K T := ⟨fun x ↦ by
    obtain ⟨c, rfl⟩ := hsurj x
    exact isSeparable_algebraMap (F := K) c⟩
  have hfinG (i) : Module.Finite (G i) T := by
    let : Module.Finite (E i) K := hfin i
    exact finite_subfield_of_map_le (E i) (G i) le_rfl
  have hdirG : Directed (· ≥ ·) G := by
    intro i j
    obtain ⟨k, hki, hkj⟩ := hdir i j
    exact ⟨k, (Subfield.gc_map_comap (algebraMap K T)).monotone_l hki,
      (Subfield.gc_map_comap (algebraMap K T)).monotone_l hkj⟩
  have hp : (pPowerSubfield K p).map (algebraMap K T) = pPowerSubfield T p :=
    map_pPowerSubfield_eq_of_surjective _ hsurj
  have hpowG (i) : pPowerSubfield T p ≤ G i := by
    rw [← hp]
    exact (Subfield.gc_map_comap (algebraMap K T)).monotone_l (hpow i)
  have hinfG : (⨅ i, G i) = pPowerSubfield T p := by
    rw [← Subfield.map_iInf, hinf, hp]
  obtain ⟨i, hi⟩ := exists_rank_stable_purelyInseparable_sameUniverse
    L p T G hfinG hdirG hpowG hinfG
  have := Algebra.FormallyEtale.of_isSeparable K T
  exact ⟨i, fun R _ _ _ _ _ hR ↦ finrank_kaehlerDifferential_eq_of_tower (T := T)
    (hi R fun _ ⟨r, hr⟩ ↦ hr ▸ (Subfield.mem_map.mpr ⟨algebraMap R K r, hR ⟨r, rfl⟩,
          (IsScalarTower.algebraMap_apply R K T r).symm⟩))
    finrank_kaehlerDifferential_of_formallyEtale⟩

/-- 有限拡大一般での階数安定。有限p-rankは要求しない。 -/
theorem exists_subfieldFamily_rank_stable_of_finite
    {K : Type u} {L : Type v} {ι : Type t} [Field K] [Field L] [Algebra K L]
    {p : ℕ} [Fact p.Prime] [CharP K p] [CharP L p] [Module.Finite K L] [Nonempty ι]
    (E : ι → Subfield K) (hfin : ∀ i, Module.Finite (E i) K)
    (hdir : Directed (· ≥ ·) E)
    (hpow : ∀ i, pPowerSubfield K p ≤ E i)
    (hinf : (⨅ i, E i) = pPowerSubfield K p) :
    ∃ i, ∀ (R : Type w) [Field R] [Algebra R K] [Algebra R L]
      [IsScalarTower R K L] [Module.Finite R K],
      Set.range (algebraMap R K) ⊆ E i →
      Module.finrank L (KaehlerDifferential R L) = Module.finrank K (KaehlerDifferential R K) := by
  let T := separableClosure K L
  let : CharP T p := (algebraMap T L).charP (algebraMap T L).injective p
  let G := fun i ↦ (E i).map (algebraMap K T) ⊔ pPowerSubfield T p
  have hG : (⨅ i, G i) = pPowerSubfield T p :=
    iInf_subfield_sup_pPower_of_isSeparable E hfin hdir hpow hinf
  have hfinG (i) : Module.Finite (G i) T := by
    let : Module.Finite (E i) K := hfin i
    exact finite_subfield_sup_pPower (E i)
  obtain ⟨i, hi⟩ := exists_subfieldFamily_rank_stable_of_isPurelyInseparable (K := T) (L := L)
    G hfinG (directed_subfield_sup_pPower E hdir) (fun _ ↦ le_sup_right) hG
  have := Algebra.FormallyEtale.of_isSeparable K T
  exact ⟨i, fun R _ _ _ _ _ hR ↦ finrank_kaehlerDifferential_eq_of_tower (T := T)
    (hi R fun _ ⟨r, hr⟩ ↦ hr ▸ (show (E i).map (algebraMap K T) ≤ G i from le_sup_left)
        (Subfield.mem_map.mpr ⟨algebraMap R K r, hR ⟨r, rfl⟩,
          (IsScalarTower.algebraMap_apply R K T r).symm⟩))
    finrank_kaehlerDifferential_of_formallyEtale⟩

/-- 有限拡大で十分小さい指標を選ぶと、その下の任意の共有限部分体で次元が等しい。 -/
theorem exists_subfieldFamily_rank_stable
    {K : Type u} {L : Type v} {ι : Type t} [Field K] [Field L] [Algebra K L]
    {p : ℕ} [Fact p.Prime] [CharP K p] [CharP L p] [Module.Finite K L] [Nonempty ι]
    (E : ι → Subfield K) (hfin : ∀ i, Module.Finite (E i) K)
    (hdir : Directed (· ≥ ·) E)
    (hpow : ∀ i, pPowerSubfield K p ≤ E i)
    (hinf : (⨅ i, E i) = pPowerSubfield K p) :
    ∃ i, ∀ R : Subfield K, Module.Finite R K → R ≤ E i →
      letI : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
      letI : Module R L := @Algebra.toModule _ _ _ _ (inferInstance : Algebra R L)
      letI : SMul R L := (inferInstance : Algebra R L).toSMul
      Module.finrank L (KaehlerDifferential R L) = Module.finrank K (KaehlerDifferential R K) := by
  obtain ⟨i, hi⟩ := exists_subfieldFamily_rank_stable_of_finite (L := L) E hfin hdir hpow hinf
  refine ⟨i, ?_⟩
  intro R hRfin hR
  let : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  let : Module R L := @Algebra.toModule _ _ _ _ (inferInstance : Algebra R L)
  let : SMul R L := (inferInstance : Algebra R L).toSMul
  let : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Finite R K := hRfin
  exact hi R (by rintro _ ⟨r, rfl⟩; exact hR r.property)

end FiniteExtension

end SerrePositivity
