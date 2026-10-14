module

public import SerrePositivity.FieldTheory.PowerSubfieldMap
public import SerrePositivity.FieldTheory.SubfieldFiniteExtension
public import SerrePositivity.FieldTheory.PrimeRootPowerSubfield
public import SerrePositivity.FieldTheory.SeparablePowerSubfieldIntersection

/-! # 拡大の塔に沿う共有限部分体族の保存

E_iの像に拡大後のp乗部分体を添加する操作について、
有限性・下向き有向性と、次の分離的／次数pの段階での交わりを接続する。
-/

@[expose] public noncomputable section
namespace SerrePositivity
variable {K L M ι : Type*} [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  {p : ℕ} [Fact p.Prime] [CharP K p] [CharP L p] [CharP M p]

omit [CharP K p] in
/-- 共有限な部分体の像にp乗部分体を添加しても、有限拡大後には共有限。 -/
theorem finite_subfield_sup_pPower [Module.Finite K L]
    (E : Subfield K) [Module.Finite E K] :
    Module.Finite ↥(E.map (algebraMap K L) ⊔ pPowerSubfield L p) L :=
  finite_subfield_of_map_le E _ le_sup_left

omit [CharP K p] in
/-- 下向き有向性は、像とp乗部分体の添加に沿って保存される。 -/
theorem directed_subfield_sup_pPower (E : ι → Subfield K)
    (hdir : ∀ i j, ∃ k, E k ≤ E i ∧ E k ≤ E j) :
    ∀ i j, ∃ k,
      (E k).map (algebraMap K L) ⊔ pPowerSubfield L p ≤
        (E i).map (algebraMap K L) ⊔ pPowerSubfield L p ∧
      (E k).map (algebraMap K L) ⊔ pPowerSubfield L p ≤
        (E j).map (algebraMap K L) ⊔ pPowerSubfield L p := by
  intro i j
  obtain ⟨k, hki, hkj⟩ := hdir i j
  exact ⟨k, sup_le_sup_right ((Subfield.gc_map_comap (algebraMap K L)).monotone_l hki) _,
    sup_le_sup_right ((Subfield.gc_map_comap (algebraMap K L)).monotone_l hkj) _⟩

omit [CharP K p] in
/-- 既に交わりを確認した族に次数pの段階を接続し、合成した拡大での交わりを得る。
先の段階の交わりは帰納仮定として受け、次の段階は既存のp乗根の定理で証明する。 -/
theorem iInf_subfield_sup_pPower_tower_primeRoot
    (E : ι → Subfield K) (hdir : ∀ i j, ∃ k, E k ≤ E i ∧ E k ≤ E j)
    (hinfL : (⨅ i, (E i).map (algebraMap K L) ⊔ pPowerSubfield L p) = pPowerSubfield L p)
    (x : M) (a : L) (hpow : x ^ p = algebraMap L M a)
    (hx : x ∉ Set.range (algebraMap L M)) (hs : Algebra.adjoin L {x} = ⊤) :
    (⨅ i, (E i).map (algebraMap K M) ⊔ pPowerSubfield M p) = pPowerSubfield M p := by
  have h := iInf_subfield_sup_pPower_primeRoot
    (fun i ↦ (E i).map (algebraMap K L) ⊔ pPowerSubfield L p)
    (directed_subfield_sup_pPower E hdir) (fun _ ↦ le_sup_right) hinfL x a hpow hx hs
  simpa only [map_subfield_sup_pPower_tower] using h

omit [CharP K p] in
/-- 既に交わりを確認した共有限な族に分離的有限拡大を接続する。 -/
theorem iInf_subfield_sup_pPower_tower_of_isSeparable
    [Module.Finite K L] [Module.Finite L M] [Algebra.IsSeparable L M] [Nonempty ι]
    (E : ι → Subfield K) (hfin : ∀ i, Module.Finite (E i) K)
    (hdir : ∀ i j, ∃ k, E k ≤ E i ∧ E k ≤ E j)
    (hinfL : (⨅ i, (E i).map (algebraMap K L) ⊔ pPowerSubfield L p) = pPowerSubfield L p) :
    (⨅ i, (E i).map (algebraMap K M) ⊔ pPowerSubfield M p) = pPowerSubfield M p := by
  have hfinL (i) : Module.Finite ↥((E i).map (algebraMap K L) ⊔ pPowerSubfield L p) L := by
    let : Module.Finite (E i) K := hfin i
    exact finite_subfield_sup_pPower (E i)
  have h := iInf_subfield_sup_pPower_of_isSeparable (K := L) (L := M)
    (fun i ↦ (E i).map (algebraMap K L) ⊔ pPowerSubfield L p) hfinL
    (directed_subfield_sup_pPower E hdir) (fun _ ↦ le_sup_right) hinfL
  simpa only [map_subfield_sup_pPower_tower] using h

end SerrePositivity
