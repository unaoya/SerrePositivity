module

public import SerrePositivity.FieldTheory.FiniteExponentOneConstants
public import SerrePositivity.FieldTheory.PrimeRootDifferentialKernel

/-! # 共有限な部分体族に対する次数pの階数安定

各部分体の有限性・p乗部分体の包含・交わりを確認して、次数pの段階を証明する。
この一段では族の有向性は不要。一般有限拡大への帰納は `FiniteExtensionDifferentialRank` で接続する。
-/

@[expose] public noncomputable section
namespace SerrePositivity
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

end SerrePositivity
