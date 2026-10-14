module

public import SerrePositivity.FieldTheory.PBasis
public import Mathlib.RingTheory.AlgebraTower

/-! # p乗部分体の写像と拡大の塔

p乗部分体は体の準同型でp乗部分体へ写る。
この包含により、拡大後の族を二段階で構成する操作は合成した拡大での構成と一致する。
-/

@[expose] public section
namespace SerrePositivity
variable {K L M : Type*} [Field K] [Field L] [Field M]
  {p : ℕ} [Fact p.Prime] [CharP K p] [CharP L p] [CharP M p]

/-- 体の準同型はp乗部分体をp乗部分体へ送る。 -/
theorem map_pPowerSubfield_le (f : K →+* L) :
    (pPowerSubfield K p).map f ≤ pPowerSubfield L p := by
  rintro _ ⟨c, hc, rfl⟩
  obtain ⟨d, hd⟩ := (mem_pPowerSubfield K p c).mp hc
  exact (mem_pPowerSubfield L p _).mpr ⟨f d, by rw [← map_pow, hd]⟩

/-- 全射な体準同型ではp乗部分体の像もp乗部分体全体になる。 -/
theorem map_pPowerSubfield_eq_of_surjective (f : K →+* L) (hf : Function.Surjective f) :
    (pPowerSubfield K p).map f = pPowerSubfield L p := by
  apply le_antisymm (map_pPowerSubfield_le f)
  intro y hy
  obtain ⟨z, hz⟩ := (mem_pPowerSubfield L p y).mp hy
  obtain ⟨c, rfl⟩ := hf z
  exact Subfield.mem_map.mpr ⟨c ^ p, (mem_pPowerSubfield K p _).mpr ⟨c, rfl⟩,
    by rw [map_pow]; exact hz⟩

/-- 自明な拡大では、元の族の交わりを写すだけで拡大後の交わりを計算できる。 -/
theorem iInf_subfield_sup_pPower_of_surjective {ι : Type*} [Nonempty ι]
    [Algebra K L] (E : ι → Subfield K)
    (hf : Function.Surjective (algebraMap K L))
    (hpow : ∀ i, pPowerSubfield K p ≤ E i)
    (hinf : (⨅ i, E i) = pPowerSubfield K p) :
    (⨅ i, (E i).map (algebraMap K L) ⊔ pPowerSubfield L p) = pPowerSubfield L p := by
  have hp := map_pPowerSubfield_eq_of_surjective (algebraMap K L) hf
  have heq (i) : (E i).map (algebraMap K L) ⊔ pPowerSubfield L p =
      (E i).map (algebraMap K L) := by
    rw [← hp]
    exact sup_eq_left.mpr ((Subfield.gc_map_comap (algebraMap K L)).monotone_l (hpow i))
  simp_rw [heq]
  rw [← Subfield.map_iInf, hinf, hp]

omit [CharP K p] in
/-- E↦Eの像⊔p乗部分体という拡大後の族の構成は、拡大の塔に沿って合成できる。 -/
theorem map_subfield_sup_pPower_tower
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M] (E : Subfield K) :
    (E.map (algebraMap K L) ⊔ pPowerSubfield L p).map (algebraMap L M) ⊔
        pPowerSubfield M p = E.map (algebraMap K M) ⊔ pPowerSubfield M p := by
  rw [Subfield.map_sup, Subfield.map_map, ← IsScalarTower.algebraMap_eq K L M,
    sup_assoc, sup_eq_right.mpr (map_pPowerSubfield_le (algebraMap L M))]

end SerrePositivity
