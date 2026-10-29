module

public import SerrePositivity.FieldTheory.FiniteExtensionPowerSubfieldIntersection
public import SerrePositivity.FieldTheory.SubfieldFamilyPrimeRootRank
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.TensorProduct.Finite

/-! # 有限拡大での通常微分の階数安定

共有限な部分体族の交わりがK^pなら、十分小さい同じ底体R上で、有限拡大後も微分の次元が等しい。
各中間体でRの作用を指定した写像の合成から取り、等号を同じR上で合成する。
-/

@[expose] public noncomputable section
namespace SerrePositivity
universe u v w t

private theorem exists_rank_stable_purelyInseparable_sameUniverse
    (L : Type v) [Field L] (p : ℕ) [Fact p.Prime] [CharP L p]
    {ι : Type t} [Nonempty ι] :
    ∀ (K : Type v) [Field K] [Algebra K L] [CharP K p]
      [IsPurelyInseparable K L] [Module.Finite K L],
      ∀ (E : ι → Subfield K), (∀ i, Module.Finite (E i) K) →
        (∀ i j, ∃ k, E k ≤ E i ∧ E k ≤ E j) →
        (∀ i, pPowerSubfield K p ≤ E i) →
        (⨅ i, E i) = pPowerSubfield K p →
        ∃ i, ∀ (R : Type w) [Field R] [Algebra R K] [Algebra R L]
          [IsScalarTower R K L] [Module.Finite R K],
          Set.range (algebraMap R K) ⊆ E i →
          Module.finrank L (KaehlerDifferential R L) =
            Module.finrank K (KaehlerDifferential R K) := by
  intro K _ _ _ _ _
  generalize hd : Module.finrank K L = d
  induction d using Nat.strongRecOn generalizing K with
  | ind d IH =>
    intro E hfin hdir hpow hinf
    by_cases hsurj : Function.Surjective (algebraMap K L)
    · let : Algebra.IsSeparable K L := ⟨fun x ↦ by
        obtain ⟨c, rfl⟩ := hsurj x
        exact isSeparable_algebraMap (F := K) c⟩
      refine ⟨Classical.arbitrary ι, ?_⟩
      intro R _ _ _ _ _ _
      have := Algebra.FormallyEtale.of_isSeparable K L
      rw [← (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R K L).finrank_eq,
        Module.finrank_baseChange]
    obtain ⟨x, a, hxp, hx, _, hlt⟩ := exists_primeRoot_step_of_isPurelyInseparable hsurj
    let T := IntermediateField.adjoin K {x}
    let : CharP T p := (algebraMap T L).charP (algebraMap T L).injective p
    let : IsPurelyInseparable T L := IsPurelyInseparable.tower_top K T L
    let xT : T := IntermediateField.AdjoinSimple.gen K x
    obtain ⟨hpT, hxT, hsT⟩ := primeRoot_adjoin_gen_properties x a hxp hx
    obtain ⟨j, hj⟩ := exists_subfieldFamily_primeRoot_rank_stable_of_range E hfin hpow hinf
      xT a hpT hxT hsT
    let G := fun i ↦ (E i).map (algebraMap K T) ⊔ pPowerSubfield T p
    have hG : (⨅ i, G i) = pPowerSubfield T p :=
      iInf_subfield_sup_pPower_primeRoot E hdir hpow hinf xT a hpT hxT hsT
    have hfinG (i) : Module.Finite (G i) T := by
      let : Module.Finite (E i) K := hfin i
      exact finite_subfield_sup_pPower (E i)
    obtain ⟨i, hi⟩ := IH (Module.finrank T L) (hd ▸ hlt) T rfl G hfinG
      (directed_subfield_sup_pPower E hdir) (fun _ ↦ le_sup_right) hG
    obtain ⟨k, hki, hkj⟩ := hdir i j
    refine ⟨k, ?_⟩
    intro R _ _ _ _ _ hR
    let : Algebra R T := ((algebraMap K T).comp (algebraMap R K)).toAlgebra
    let : Module R T := @Algebra.toModule _ _ _ _ (inferInstance : Algebra R T)
    let : SMul R T := (inferInstance : Algebra R T).toSMul
    let : IsScalarTower R K T := IsScalarTower.of_algebraMap_eq' rfl
    let : IsScalarTower R T L := IsScalarTower.of_algebraMap_eq' (by
      change algebraMap R L = (algebraMap K L).comp (algebraMap R K)
      exact IsScalarTower.algebraMap_eq R K L)
    let : Module.Finite R T := Module.Finite.trans (R := R) K T
    have hrT : Set.range (algebraMap R T) ⊆ G i := by
      rintro _ ⟨r, rfl⟩
      apply (show (E i).map (algebraMap K T) ≤ G i from le_sup_left)
      exact Subfield.mem_map.mpr ⟨algebraMap R K r, hki (hR ⟨r, rfl⟩), rfl⟩
    exact (hi R hrT).trans (hj R (fun _ hr ↦ hkj (hR hr)))

/-- 有限純非分離拡大での階数安定。同じ底体と同じ指定済みの作用で比較する。 -/
theorem exists_subfieldFamily_rank_stable_of_isPurelyInseparable
    {K : Type u} {L : Type v} {ι : Type t} [Field K] [Field L] [Algebra K L]
    {p : ℕ} [Fact p.Prime] [CharP K p] [CharP L p]
    [Module.Finite K L] [IsPurelyInseparable K L] [Nonempty ι]
    (E : ι → Subfield K) (hfin : ∀ i, Module.Finite (E i) K)
    (hdir : ∀ i j, ∃ k, E k ≤ E i ∧ E k ≤ E j)
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
  have hdirG : ∀ i j, ∃ k, G k ≤ G i ∧ G k ≤ G j := by
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
  refine ⟨i, ?_⟩
  intro R _ _ _ _ _ hR
  let : Algebra R T := ((algebraMap K T).comp (algebraMap R K)).toAlgebra
  let : Module R T := @Algebra.toModule _ _ _ _ (inferInstance : Algebra R T)
  let : SMul R T := (inferInstance : Algebra R T).toSMul
  let : IsScalarTower R K T := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R T L := IsScalarTower.of_algebraMap_eq' (by
    change algebraMap R L = (algebraMap K L).comp (algebraMap R K)
    exact IsScalarTower.algebraMap_eq R K L)
  let : Module.Finite R T := Module.Finite.trans (R := R) K T
  have hrT : Set.range (algebraMap R T) ⊆ G i := by
    rintro _ ⟨r, rfl⟩
    exact Subfield.mem_map.mpr ⟨algebraMap R K r, hR ⟨r, rfl⟩, rfl⟩
  have := Algebra.FormallyEtale.of_isSeparable K T
  rw [hi R hrT, ← (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R K T).finrank_eq,
    Module.finrank_baseChange]

/-- 有限拡大一般での階数安定。有限p-rankは要求しない。 -/
theorem exists_subfieldFamily_rank_stable_of_finite
    {K : Type u} {L : Type v} {ι : Type t} [Field K] [Field L] [Algebra K L]
    {p : ℕ} [Fact p.Prime] [CharP K p] [CharP L p] [Module.Finite K L] [Nonempty ι]
    (E : ι → Subfield K) (hfin : ∀ i, Module.Finite (E i) K)
    (hdir : ∀ i j, ∃ k, E k ≤ E i ∧ E k ≤ E j)
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
  refine ⟨i, ?_⟩
  intro R _ _ _ _ _ hR
  let : Algebra R T := ((algebraMap K T).comp (algebraMap R K)).toAlgebra
  let : Module R T := @Algebra.toModule _ _ _ _ (inferInstance : Algebra R T)
  let : SMul R T := (inferInstance : Algebra R T).toSMul
  let : IsScalarTower R K T := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R T L := IsScalarTower.of_algebraMap_eq' (by
    change algebraMap R L = (algebraMap K L).comp (algebraMap R K)
    exact IsScalarTower.algebraMap_eq R K L)
  let : Module.Finite R T := Module.Finite.trans (R := R) K T
  have hrT : Set.range (algebraMap R T) ⊆ G i := by
    rintro _ ⟨r, rfl⟩
    apply (show (E i).map (algebraMap K T) ≤ G i from le_sup_left)
    exact Subfield.mem_map.mpr ⟨algebraMap R K r, hR ⟨r, rfl⟩, rfl⟩
  have := Algebra.FormallyEtale.of_isSeparable K T
  rw [hi R hrT, ← (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R K T).finrank_eq,
    Module.finrank_baseChange]

/-- 有限拡大で十分小さい指標を選ぶと、その下の任意の共有限部分体で次元が等しい。 -/
theorem exists_subfieldFamily_rank_stable
    {K : Type u} {L : Type v} {ι : Type t} [Field K] [Field L] [Algebra K L]
    {p : ℕ} [Fact p.Prime] [CharP K p] [CharP L p] [Module.Finite K L] [Nonempty ι]
    (E : ι → Subfield K) (hfin : ∀ i, Module.Finite (E i) K)
    (hdir : ∀ i j, ∃ k, E k ≤ E i ∧ E k ≤ E j)
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

end SerrePositivity
