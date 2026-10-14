module

public import SerrePositivity.FieldTheory.PurelyInseparablePrimeStep
public import SerrePositivity.FieldTheory.SubfieldFamilyTower

/-! # 一般有限拡大後のp乗部分体族の交わり

純非分離な場合は次数pの添加で残りの拡大次数を減らして帰納する。
一般の場合はMathlibの分離閉包とその上の純非分離性を使って二つの段階を接続する。
-/

@[expose] public noncomputable section
namespace SerrePositivity

universe u v w

private theorem iInf_pPower_purelyInseparable_sameUniverse
    (L : Type v) [Field L] (p : ℕ) [Fact p.Prime] [CharP L p]
    {ι : Type w} [Nonempty ι] :
    ∀ (K : Type v) [Field K] [Algebra K L] [CharP K p]
      [IsPurelyInseparable K L] [Module.Finite K L],
      ∀ (E : ι → Subfield K), (∀ i, Module.Finite (E i) K) →
        (∀ i j, ∃ k, E k ≤ E i ∧ E k ≤ E j) →
        (∀ i, pPowerSubfield K p ≤ E i) →
        (⨅ i, E i) = pPowerSubfield K p →
        (⨅ i, (E i).map (algebraMap K L) ⊔ pPowerSubfield L p) = pPowerSubfield L p := by
  intro K _ _ _ _ _
  generalize hd : Module.finrank K L = d
  induction d using Nat.strongRecOn generalizing K with
  | ind d IH =>
    intro E hfin hdir hpow hinf
    by_cases hsurj : Function.Surjective (algebraMap K L)
    · exact iInf_subfield_sup_pPower_of_surjective E hsurj hpow hinf
    obtain ⟨x, a, hxp, hx, _, hlt⟩ := exists_primeRoot_step_of_isPurelyInseparable hsurj
    let T := IntermediateField.adjoin K {x}
    let : CharP T p := (algebraMap T L).charP (algebraMap T L).injective p
    let : IsPurelyInseparable T L := IsPurelyInseparable.tower_top K T L
    let xT : T := IntermediateField.AdjoinSimple.gen K x
    obtain ⟨hpT, hxT, hsT⟩ := primeRoot_adjoin_gen_properties x a hxp hx
    let G := fun i ↦ (E i).map (algebraMap K T) ⊔ pPowerSubfield T p
    have hG : (⨅ i, G i) = pPowerSubfield T p :=
      iInf_subfield_sup_pPower_primeRoot E hdir hpow hinf xT a hpT hxT hsT
    have hfinG (i) : Module.Finite (G i) T := by
      let : Module.Finite (E i) K := hfin i
      exact finite_subfield_sup_pPower (E i)
    have hdirG := directed_subfield_sup_pPower (L := T) E hdir
    have h := IH (Module.finrank T L) (hd ▸ hlt) T rfl G hfinG hdirG
      (fun _ ↦ le_sup_right) hG
    simpa only [G, map_subfield_sup_pPower_tower] using h

/-- 一般の有限純非分離拡大で、拡大後の族の交わりはp乗部分体。
拡大の始域と終域の宇宙は異なっていてもよい。 -/
theorem iInf_subfield_sup_pPower_of_isPurelyInseparable
    {K : Type u} {L : Type v} {ι : Type w} [Field K] [Field L] [Algebra K L]
    {p : ℕ} [Fact p.Prime] [CharP K p] [CharP L p]
    [Module.Finite K L] [IsPurelyInseparable K L] [Nonempty ι]
    (E : ι → Subfield K) (hfin : ∀ i, Module.Finite (E i) K)
    (hdir : ∀ i j, ∃ k, E k ≤ E i ∧ E k ≤ E j)
    (hpow : ∀ i, pPowerSubfield K p ≤ E i)
    (hinf : (⨅ i, E i) = pPowerSubfield K p) :
    (⨅ i, (E i).map (algebraMap K L) ⊔ pPowerSubfield L p) = pPowerSubfield L p := by
  let T : IntermediateField K L := ⊥
  let : CharP T p := (algebraMap T L).charP (algebraMap T L).injective p
  let : IsPurelyInseparable T L := IsPurelyInseparable.tower_top K T L
  let G := fun i ↦ (E i).map (algebraMap K T)
  have hsurj : Function.Surjective (algebraMap K T) := by
    intro t
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp t.property
    exact ⟨c, Subtype.ext hc⟩
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
  have h := iInf_pPower_purelyInseparable_sameUniverse L p T G hfinG hdirG hpowG hinfG
  simpa only [G, Subfield.map_map, ← IsScalarTower.algebraMap_eq K T L] using h

/-- 有限拡大一般で、拡大後の共有限部分体族の交わりはp乗部分体。
分離閉包までの分離的段階と、その上の純非分離的段階を接続する。 -/
theorem iInf_subfield_sup_pPower_of_finite
    {K : Type u} {L : Type v} {ι : Type w} [Field K] [Field L] [Algebra K L]
    {p : ℕ} [Fact p.Prime] [CharP K p] [CharP L p]
    [Module.Finite K L] [Nonempty ι]
    (E : ι → Subfield K) (hfin : ∀ i, Module.Finite (E i) K)
    (hdir : ∀ i j, ∃ k, E k ≤ E i ∧ E k ≤ E j)
    (hpow : ∀ i, pPowerSubfield K p ≤ E i)
    (hinf : (⨅ i, E i) = pPowerSubfield K p) :
    (⨅ i, (E i).map (algebraMap K L) ⊔ pPowerSubfield L p) = pPowerSubfield L p := by
  let T := separableClosure K L
  let : CharP T p := (algebraMap T L).charP (algebraMap T L).injective p
  let G := fun i ↦ (E i).map (algebraMap K T) ⊔ pPowerSubfield T p
  have hG : (⨅ i, G i) = pPowerSubfield T p :=
    iInf_subfield_sup_pPower_of_isSeparable E hfin hdir hpow hinf
  have hfinG (i) : Module.Finite (G i) T := by
    let : Module.Finite (E i) K := hfin i
    exact finite_subfield_sup_pPower (E i)
  have h := iInf_subfield_sup_pPower_of_isPurelyInseparable (K := T) (L := L) G hfinG
    (directed_subfield_sup_pPower E hdir) (fun _ ↦ le_sup_right) hG
  simpa only [G, map_subfield_sup_pPower_tower] using h

end SerrePositivity
