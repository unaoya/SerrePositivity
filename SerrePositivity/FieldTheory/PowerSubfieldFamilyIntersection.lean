module

public import SerrePositivity.FieldTheory.SubfieldLinearAlgebra
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import SerrePositivity.FieldTheory.PrimeRootPowerSubfield
public import SerrePositivity.FieldTheory.PurelyInseparablePrimeStep

/-! # 有限拡大後の p 乗部分体の族の交わり

概要：交わりが `K^p` の、共有限で下向き有向な部分体族 `Eᵢ` について、有限拡大 `L/K` の後も
`⋂ (Eᵢ · L^p) = L^p`（`iInf_subfield_sup_pPower_of_finite`）。
方針：分離的な場合は、`L^p` が基底の p 乗の `K^p` 上の線形包であること（分離性で p 乗が独立）から計算する。
純非分離な場合は p 乗根の添加ごとに次数の帰納を行う。一般の場合は分離閉包で二段に分ける。
規約：底体の有限 p-rank は要求しない。
使われ方：共有限な中間係数体の族（CommutativeAlgebra の Cofinite 系）、階数の安定（`SubfieldFamilyDifferentialRank`）。
-/

@[expose] public noncomputable section
namespace SerrePositivity

section Map

variable {K L M : Type*} [Field K] [Field L] [Field M]
  {p : ℕ} [Fact p.Prime] [CharP K p] [CharP L p] [CharP M p]

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

end Map

section Separable

variable {K L τ ι : Type*} [Field K] [Field L] [Algebra K L]
  {p : ℕ} [Fact p.Prime] [CharP K p] [CharP L p]

/-- 任意の有限基底のp乗は、拡大のp乗部分体を底体のp乗部分体の像上で張る。
この生成性の計算には分離性は不要。 -/
theorem pPowerSubfield_eq_span_pow_basis [Finite τ] (B : Module.Basis τ K L) :
    (pPowerSubfield L p : Set L) =
      (Submodule.span ((pPowerSubfield K p).map (algebraMap K L))
        (Set.range (fun i ↦ B i ^ p)) : Set L) := by
  classical
  let := Fintype.ofFinite τ
  let F := (pPowerSubfield K p).map (algebraMap K L)
  have hF : F ≤ pPowerSubfield L p := map_pPowerSubfield_le (algebraMap K L)
  ext z
  constructor
  · intro hz
    obtain ⟨y, rfl⟩ := (mem_pPowerSubfield L p z).mp hz
    apply (Submodule.mem_span_range_iff_exists_fun F).mpr
    let c : τ → F := fun i ↦ ⟨algebraMap K L (B.repr y i) ^ p,
      Subfield.mem_map.mpr ⟨(B.repr y i) ^ p,
        (mem_pPowerSubfield K p _).mpr ⟨_, rfl⟩, map_pow _ _ _⟩⟩
    refine ⟨c, ?_⟩
    have heq := congrArg (frobenius L p) (B.sum_repr y)
    simpa [Algebra.smul_def, Subfield.algebraMap_ofSubfield, c, map_sum, map_mul,
      frobenius_def] using heq
  · intro hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact (mem_pPowerSubfield L p _).mpr ⟨B i, rfl⟩
    | zero => exact (pPowerSubfield L p).zero_mem
    | add x y _ _ hx hy => exact (pPowerSubfield L p).add_mem hx hy
    | smul c x _ hx =>
      change (c : L) * x ∈ pPowerSubfield L p
      exact (pPowerSubfield L p).mul_mem (hF c.property) hx

/-- 共有限な下向き有向族の交わりがK^pなら、分離的有限拡大後の族の交わりはL^p。
底体の有限p-rankは要求しない。 -/
theorem iInf_subfield_sup_pPower_of_isSeparable
    [Module.Finite K L] [Algebra.IsSeparable K L] [Nonempty ι]
    (E : ι → Subfield K) (hfin : ∀ i, Module.Finite (E i) K)
    (hdir : Directed (· ≥ ·) E)
    (hpow : ∀ i, pPowerSubfield K p ≤ E i)
    (hinf : (⨅ i, E i) = pPowerSubfield K p) :
    (⨅ i, (E i).map (algebraMap K L) ⊔ pPowerSubfield L p) = pPowerSubfield L p := by
  classical
  let B := Module.finBasis K L
  let v := fun i ↦ B i ^ p
  let F := (pPowerSubfield K p).map (algebraMap K L)
  let E' := fun i ↦ (E i).map (algebraMap K L)
  have hspan : (pPowerSubfield L p : Set L) = (Submodule.span F (Set.range v) : Set L) :=
    pPowerSubfield_eq_span_pow_basis B
  have hv : LinearIndependent K v := by
    simpa [v, pow_one] using B.linearIndependent.map_pow_expChar_pow_of_isSeparable p 1
  have hE' (i) : E' i ≤ (algebraMap K L).fieldRange := by
    rintro _ ⟨c, _, rfl⟩
    exact ⟨c, rfl⟩
  have hind : ∃ j, LinearIndependent (E' j) v :=
    ⟨Classical.arbitrary ι, linearIndependent_subfield_of_le (hE' _) v
      (linearIndependent_fieldRange v hv)⟩
  have hdir' : Directed (· ≥ ·) E' := by
    intro i j
    obtain ⟨k, hki, hkj⟩ := hdir i j
    exact ⟨k, (Subfield.gc_map_comap (algebraMap K L)).monotone_l hki,
      (Subfield.gc_map_comap (algebraMap K L)).monotone_l hkj⟩
  have hinf' : (⨅ i, E' i) = F := by
    rw [← Subfield.map_iInf, hinf]
  have hmem (i) (z : L) : z ∈ E' i ⊔ pPowerSubfield L p ↔
      z ∈ Submodule.span (E' i) (Set.range v) := by
    let : Module.Finite (E i) K := hfin i
    let : Module.Finite (E' i) L := finite_subfield_of_map_le (E i) (E' i) le_rfl
    exact mem_subfield_sup_iff_mem_span F (E' i) (pPowerSubfield L p)
      ((Subfield.gc_map_comap (algebraMap K L)).monotone_l (hpow i)) v hspan z
  ext z
  simp only [Subfield.mem_iInf]
  change (∀ i, z ∈ E' i ⊔ pPowerSubfield L p) ↔ z ∈ pPowerSubfield L p
  simp_rw [hmem]
  rw [mem_all_subfield_spans_iff E' hdir' v hind, hinf']
  exact (Set.ext_iff.mp hspan z).symm

end Separable

section Tower

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
    (hdir : Directed (· ≥ ·) E) :
    Directed (· ≥ ·) fun i ↦ (E i).map (algebraMap K L) ⊔ pPowerSubfield L p := by
  intro i j
  obtain ⟨k, hki, hkj⟩ := hdir i j
  exact ⟨k, sup_le_sup_right ((Subfield.gc_map_comap (algebraMap K L)).monotone_l hki) _,
    sup_le_sup_right ((Subfield.gc_map_comap (algebraMap K L)).monotone_l hkj) _⟩

omit [CharP K p] in
/-- 既に交わりを確認した族に次数pの段階を接続し、合成した拡大での交わりを得る。
先の段階の交わりは帰納仮定として受け、次の段階は既存のp乗根の定理で証明する。 -/
theorem iInf_subfield_sup_pPower_tower_primeRoot
    (E : ι → Subfield K) (hdir : Directed (· ≥ ·) E)
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
    (hdir : Directed (· ≥ ·) E)
    (hinfL : (⨅ i, (E i).map (algebraMap K L) ⊔ pPowerSubfield L p) = pPowerSubfield L p) :
    (⨅ i, (E i).map (algebraMap K M) ⊔ pPowerSubfield M p) = pPowerSubfield M p := by
  have hfinL (i) : Module.Finite ↥((E i).map (algebraMap K L) ⊔ pPowerSubfield L p) L := by
    let : Module.Finite (E i) K := hfin i
    exact finite_subfield_sup_pPower (E i)
  have h := iInf_subfield_sup_pPower_of_isSeparable (K := L) (L := M)
    (fun i ↦ (E i).map (algebraMap K L) ⊔ pPowerSubfield L p) hfinL
    (directed_subfield_sup_pPower E hdir) (fun _ ↦ le_sup_right) hinfL
  simpa only [map_subfield_sup_pPower_tower] using h

end Tower

section FiniteExtension

universe u v w

private theorem iInf_pPower_purelyInseparable_sameUniverse
    (L : Type v) [Field L] (p : ℕ) [Fact p.Prime] [CharP L p]
    {ι : Type w} [Nonempty ι] :
    ∀ (K : Type v) [Field K] [Algebra K L] [CharP K p]
      [IsPurelyInseparable K L] [Module.Finite K L],
      ∀ (E : ι → Subfield K), (∀ i, Module.Finite (E i) K) →
        Directed (· ≥ ·) E →
        (∀ i, pPowerSubfield K p ≤ E i) →
        (⨅ i, E i) = pPowerSubfield K p →
        (⨅ i, (E i).map (algebraMap K L) ⊔ pPowerSubfield L p) = pPowerSubfield L p := by
  intro K _ _ _ _ _
  refine induction_on_primeRoot_of_isPurelyInseparable (p := p)
    (P := fun K [Field K] [Algebra K L] ↦ ∀ [CharP K p] (E : ι → Subfield K),
      (∀ i, Module.Finite (E i) K) → Directed (· ≥ ·) E → (∀ i, pPowerSubfield K p ≤ E i) →
      (⨅ i, E i) = pPowerSubfield K p →
      (⨅ i, (E i).map (algebraMap K L) ⊔ pPowerSubfield L p) = pPowerSubfield L p) ?_ ?_ K
  · intro K _ _ hsurj _ E _ _ hpow hinf
    exact iInf_subfield_sup_pPower_of_surjective E hsurj hpow hinf
  · intro K _ _ _ _ _ x a hxp hx IH _ E hfin hdir hpow hinf
    let T := IntermediateField.adjoin K {x}
    let : CharP T p := (algebraMap T L).charP (algebraMap T L).injective p
    obtain ⟨hpT, hxT, hsT⟩ := primeRoot_adjoin_gen_properties x a hxp hx
    have hfinG (i) : Module.Finite ↥((E i).map (algebraMap K T) ⊔ pPowerSubfield T p) T := by
      let : Module.Finite (E i) K := hfin i
      exact finite_subfield_sup_pPower (E i)
    have h := IH _ hfinG (directed_subfield_sup_pPower E hdir) (fun _ ↦ le_sup_right)
      (iInf_subfield_sup_pPower_primeRoot E hdir hpow hinf _ a hpT hxT hsT)
    simpa only [T, map_subfield_sup_pPower_tower] using h

/-- 一般の有限純非分離拡大で、拡大後の族の交わりはp乗部分体。
拡大の始域と終域の宇宙は異なっていてもよい。 -/
theorem iInf_subfield_sup_pPower_of_isPurelyInseparable
    {K : Type u} {L : Type v} {ι : Type w} [Field K] [Field L] [Algebra K L]
    {p : ℕ} [Fact p.Prime] [CharP K p] [CharP L p]
    [Module.Finite K L] [IsPurelyInseparable K L] [Nonempty ι]
    (E : ι → Subfield K) (hfin : ∀ i, Module.Finite (E i) K)
    (hdir : Directed (· ≥ ·) E)
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
  have h := iInf_pPower_purelyInseparable_sameUniverse L p T G hfinG hdirG hpowG hinfG
  simpa only [G, Subfield.map_map, ← IsScalarTower.algebraMap_eq K T L] using h

/-- 有限拡大一般で、拡大後の共有限部分体族の交わりはp乗部分体。
分離閉包までの分離的段階と、その上の純非分離的段階を接続する。 -/
theorem iInf_subfield_sup_pPower_of_finite
    {K : Type u} {L : Type v} {ι : Type w} [Field K] [Field L] [Algebra K L]
    {p : ℕ} [Fact p.Prime] [CharP K p] [CharP L p]
    [Module.Finite K L] [Nonempty ι]
    (E : ι → Subfield K) (hfin : ∀ i, Module.Finite (E i) K)
    (hdir : Directed (· ≥ ·) E)
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

end FiniteExtension

end SerrePositivity
