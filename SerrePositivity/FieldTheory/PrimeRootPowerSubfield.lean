module

public import SerrePositivity.FieldTheory.SubfieldPrimeRootIntersection

/-! # 一つのp乗根を添加した体のp乗部分体

L=K[x]、x^p=aなら、Lのp乗部分体はK^pにaを添加した体の像。
部分体族の交わりの計算を拡大後のp乗部分体へ接続する。
-/

@[expose] public noncomputable section
namespace SerrePositivity
variable {K L ι : Type*} [Field K] [Field L] [Algebra K L]
  {p : ℕ} [Fact p.Prime] [CharP K p] [CharP L p]

/-- 単純なp乗根添加のp乗部分体を、底体内の係数の添加として計算する。
自明な添加も含み、拡大次数の仮定は不要。 -/
theorem pPowerSubfield_primeRoot_eq_map_adjoin
    (x : L) (a : K) (hpow : x ^ p = algebraMap K L a)
    (hs : Algebra.adjoin K {x} = ⊤) :
    pPowerSubfield L p =
      (IntermediateField.adjoin (pPowerSubfield K p) {a}).toSubfield.map (algebraMap K L) := by
  let T := (IntermediateField.adjoin (pPowerSubfield K p) {a}).toSubfield
  apply le_antisymm
  · intro y hy
    obtain ⟨z, rfl⟩ := (mem_pPowerSubfield L p y).mp hy
    clear hy
    have hz : z ∈ Algebra.adjoin K {x} := by rw [hs]; trivial
    induction hz using Algebra.adjoin_induction with
    | mem z hz =>
      have hzx : z = x := Set.mem_singleton_iff.mp hz
      rw [hzx, hpow]
      exact Subfield.mem_map.mpr ⟨a, IntermediateField.mem_adjoin_simple_self _ a, rfl⟩
    | algebraMap c =>
      rw [← map_pow]
      apply Subfield.mem_map.mpr
      refine ⟨c ^ p, ?_, rfl⟩
      exact (IntermediateField.adjoin (pPowerSubfield K p) {a}).algebraMap_mem
        ⟨c ^ p, (mem_pPowerSubfield K p _).mpr ⟨c, rfl⟩⟩
    | add z w _ _ hz hw =>
      change (frobenius L p) (z + w) ∈ T.map (algebraMap K L)
      rw [map_add]
      exact (T.map (algebraMap K L)).add_mem hz hw
    | mul z w _ _ hz hw =>
      rw [mul_pow]
      exact (T.map (algebraMap K L)).mul_mem hz hw
  · apply Subfield.map_le_iff_le_comap.mpr
    apply IntermediateField.adjoin_le_subfield
    · rintro _ ⟨c, rfl⟩
      change algebraMap K L (c : K) ∈ pPowerSubfield L p
      obtain ⟨d, hd⟩ := (mem_pPowerSubfield K p (c : K)).mp c.property
      exact (mem_pPowerSubfield L p _).mpr ⟨algebraMap K L d, by rw [← map_pow, hd]⟩
    · rw [Set.singleton_subset_iff]
      exact (mem_pPowerSubfield L p _).mpr ⟨x, hpow⟩

/-- 拡大後のp乗部分体を含めた族は、底体内で係数aを添加した族の像。
次の帰納段階では左辺を部分体族として使う。 -/
theorem subfield_sup_pPower_primeRoot_eq_map_adjoin
    (E : Subfield K) (hE : pPowerSubfield K p ≤ E)
    (x : L) (a : K) (hpow : x ^ p = algebraMap K L a)
    (hs : Algebra.adjoin K {x} = ⊤) :
    E.map (algebraMap K L) ⊔ pPowerSubfield L p =
      (IntermediateField.adjoin E {a}).toSubfield.map (algebraMap K L) := by
  rw [pPowerSubfield_primeRoot_eq_map_adjoin x a hpow hs, ← Subfield.map_sup]
  congr 1
  apply le_antisymm
  · apply sup_le
    · intro c hc
      exact (IntermediateField.adjoin E {a}).algebraMap_mem ⟨c, hc⟩
    · apply IntermediateField.adjoin_le_subfield
      · rintro _ ⟨c, rfl⟩
        exact (IntermediateField.adjoin E {a}).algebraMap_mem ⟨c, hE c.property⟩
      · rw [Set.singleton_subset_iff]
        exact IntermediateField.mem_adjoin_simple_self E a
  · apply IntermediateField.adjoin_le_subfield
    · rintro _ ⟨c, rfl⟩
      exact (show E ≤ E ⊔ (IntermediateField.adjoin (pPowerSubfield K p) {a}).toSubfield
          from le_sup_left) c.property
    · rw [Set.singleton_subset_iff]
      exact (show (IntermediateField.adjoin (pPowerSubfield K p) {a}).toSubfield ≤
          E ⊔ (IntermediateField.adjoin (pPowerSubfield K p) {a}).toSubfield from le_sup_right)
          (IntermediateField.mem_adjoin_simple_self (pPowerSubfield K p) a)

/-- 次数pの非自明な添加後の族の交わりは、拡大後のp乗部分体。
各族は底体内でaを添加してからLへ写すことで与える。 -/
theorem iInf_subfieldFamily_primeRoot_eq_pPower
    (E : ι → Subfield K)
    (hdir : ∀ i j, ∃ k, E k ≤ E i ∧ E k ≤ E j)
    (hpowE : ∀ i, pPowerSubfield K p ≤ E i)
    (hinf : (⨅ i, E i) = pPowerSubfield K p)
    (x : L) (a : K) (hpow : x ^ p = algebraMap K L a)
    (hx : x ∉ Set.range (algebraMap K L)) (hs : Algebra.adjoin K {x} = ⊤) :
    (⨅ i, (IntermediateField.adjoin (E i) {a}).toSubfield.map (algebraMap K L)) =
      pPowerSubfield L p := by
  classical
  have ha : a ∉ pPowerSubfield K p := by
    intro h
    obtain ⟨c, hc⟩ := (mem_pPowerSubfield K p a).mp h
    exact primeRoot_coefficient_not_pow x a hpow hx c hc
  have hne : Nonempty ι := by
    by_contra h
    have hall : ∀ i : ι, a ∈ E i := fun i ↦ (h ⟨i⟩).elim
    exact ha (hinf ▸ Subfield.mem_iInf.mpr hall)
  let : Nonempty ι := hne
  rw [← Subfield.map_iInf, iInf_subfield_adjoin_primeRoot E hdir hpowE hinf a ha]
  exact (pPowerSubfield_primeRoot_eq_map_adjoin x a hpow hs).symm

/-- F_i(L^p)という拡大後の族の交わりは、非自明な次数pの添加ではL^p。 -/
theorem iInf_subfield_sup_pPower_primeRoot
    (E : ι → Subfield K)
    (hdir : ∀ i j, ∃ k, E k ≤ E i ∧ E k ≤ E j)
    (hpowE : ∀ i, pPowerSubfield K p ≤ E i)
    (hinf : (⨅ i, E i) = pPowerSubfield K p)
    (x : L) (a : K) (hpow : x ^ p = algebraMap K L a)
    (hx : x ∉ Set.range (algebraMap K L)) (hs : Algebra.adjoin K {x} = ⊤) :
    (⨅ i, (E i).map (algebraMap K L) ⊔ pPowerSubfield L p) = pPowerSubfield L p := by
  simp_rw [subfield_sup_pPower_primeRoot_eq_map_adjoin _ (hpowE _) x a hpow hs]
  exact iInf_subfieldFamily_primeRoot_eq_pPower E hdir hpowE hinf x a hpow hx hs

end SerrePositivity
