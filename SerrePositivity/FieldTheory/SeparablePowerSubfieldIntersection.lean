module

public import SerrePositivity.FieldTheory.PowerSubfieldMap
public import SerrePositivity.FieldTheory.SubfieldScalarSpan
public import SerrePositivity.FieldTheory.SubfieldFiniteExtension
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # 分離的有限拡大後のp乗部分体族の交わり

有限基底のp乗は、分離性により底体上で独立なまま。
p乗部分体はその族を底体のp乗部分体上で張った空間なので、
部分体の合成を共通の線形包へ直して交わりを計算する。
-/

@[expose] public noncomputable section
namespace SerrePositivity
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
    (hdir : ∀ i j, ∃ k, E k ≤ E i ∧ E k ≤ E j)
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
  have hdir' : ∀ i j, ∃ k, E' k ≤ E' i ∧ E' k ≤ E' j := by
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

end SerrePositivity
