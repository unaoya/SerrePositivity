module

public import SerrePositivity.FieldTheory.PMonomial
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.RingTheory.Derivation.Basic

/-! # Frobenius 部分体と p-basis

p-basis は有限台 p 単項式が p 乗部分体上の基底であるという数学的条件。
存在や指定持ち上げの係数体はこの定義からは仮定せず、別途証明する。
-/

@[expose] public section
namespace SerrePositivity

variable (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]

/-- `K` の p 乗部分体。 -/
def pPowerSubfield : Subfield K := (frobenius K p).fieldRange

@[simp] theorem mem_pPowerSubfield (x : K) :
    x ∈ pPowerSubfield K p ↔ ∃ y : K, y ^ p = x := Iff.rfl

theorem pPowerSubfield_eq_top_iff :
    pPowerSubfield K p = ⊤ ↔ Function.Surjective (frobenius K p) :=
  RingHom.fieldRange_eq_top_iff

theorem pPowerSubfield_eq_top_of_perfect [PerfectField K] : pPowerSubfield K p = ⊤ :=
  (pPowerSubfield_eq_top_iff K p).mpr (surjective_frobenius K p)

/-- Frobenius は体とその p 乗部分体との同型。完全体性は不要。 -/
noncomputable def pPowerEquiv : K ≃+* pPowerSubfield K p :=
  (frobenius K p).rangeRestrictFieldEquiv

@[simp] theorem pPowerEquiv_apply_coe (x : K) :
    (pPowerEquiv K p x : K) = x ^ p := rfl

/-- p 単項式が p 乗部分体上で独立で、全体を生成する族。添字の有限性は要求しない。 -/
def IsPBasis {ι : Type*} (b : ι → K) : Prop :=
  LinearIndependent (pPowerSubfield K p) (pMonomial (p := p) b) ∧
    Submodule.span (pPowerSubfield K p) (Set.range (pMonomial (p := p) b)) = ⊤

namespace IsPBasis

variable {K p} {ι : Type*} {b : ι → K}

/-- p-basis から実際の線形代数の基底を構成する。 -/
noncomputable def basis (hb : IsPBasis K p b) :
    Module.Basis (PExponent p ι) (pPowerSubfield K p) K :=
  Module.Basis.mk hb.1 (by rw [hb.2])

@[simp] theorem basis_apply (hb : IsPBasis K p b) (d : PExponent p ι) :
    hb.basis d = pMonomial b d := Module.Basis.mk_apply _ _ _

/-- p-basis による一意な有限台展開の係数の p 乗根を与える同値。
線形同値ではなく、Frobenius の逆で係数を変換した同値である。 -/
noncomputable def expansionEquiv (hb : IsPBasis K p b) : K ≃ (PExponent p ι →₀ K) :=
  hb.basis.repr.toEquiv.trans
    (Finsupp.mapRange.equiv (pPowerEquiv K p).symm.toEquiv (pPowerEquiv K p).symm.map_zero)

/-- 展開から元を復元する実際の式。添字集合が無限でも有限和である。 -/
theorem expansionEquiv_symm_apply (hb : IsPBasis K p b) (c : PExponent p ι →₀ K) :
    hb.expansionEquiv.symm c = c.sum (fun d a ↦ a ^ p * pMonomial b d) := by
  change hb.basis.repr.symm
    (Finsupp.mapRange (pPowerEquiv K p) (map_zero _) c) = _
  rw [Module.Basis.repr_symm_apply, Finsupp.linearCombination_apply,
    Finsupp.sum_mapRange_index (by intro d; simp)]
  apply Finsupp.sum_congr
  intro d _
  rw [hb.basis_apply]
  change (pPowerEquiv K p (c d) : K) * pMonomial b d = _
  rw [pPowerEquiv_apply_coe]

theorem sum_expansionEquiv (hb : IsPBasis K p b) (x : K) :
    (hb.expansionEquiv x).sum (fun d a ↦ a ^ p * pMonomial b d) = x := by
  rw [← hb.expansionEquiv_symm_apply, Equiv.symm_apply_apply]

/-- 任意の部分族の p 単項式も元の p 乗部分体上で独立。 -/
theorem linearIndependent_comp {κ : Type*} (hb : IsPBasis K p b) (e : κ ↪ ι) :
    LinearIndependent (pPowerSubfield K p) (pMonomial (p := p) (b ∘ e)) :=
  linearIndependent_pMonomial_comp hb.1 e

/-- 有限 p-basis の単項式が張る空間の次元。 -/
theorem finrank_span [Fintype ι] (hb : IsPBasis K p b) :
    Module.finrank (pPowerSubfield K p)
      (Submodule.span (pPowerSubfield K p) (Set.range (pMonomial (p := p) b))) =
        p ^ Fintype.card ι := finrank_span_pMonomial hb.1

/-- 有限 p-basis は体の p 乗部分体上の次元を計算する。 -/
theorem finrank [Fintype ι] (hb : IsPBasis K p b) :
    Module.finrank (pPowerSubfield K p) K = p ^ Fintype.card ι := by
  rw [← finrank_top, ← hb.2]
  exact hb.finrank_span

/-- p-basis の元は p 乗部分体上の代数としても体全体を生成する。 -/
theorem adjoin_eq_top (hb : IsPBasis K p b) :
    Algebra.adjoin (pPowerSubfield K p) (Set.range b) = ⊤ := by
  classical
  let A := Algebra.adjoin (pPowerSubfield K p) (Set.range b)
  have hmono (d : PExponent p ι) : pMonomial b d ∈ A := by
    apply A.prod_mem
    intro i _
    exact A.pow_mem (Algebra.subset_adjoin (Set.mem_range_self i)) _
  have hle : Submodule.span (pPowerSubfield K p)
      (Set.range (pMonomial (p := p) b)) ≤ A.toSubmodule :=
    Submodule.span_le.mpr (by rintro _ ⟨d, rfl⟩; exact hmono d)
  apply top_le_iff.mp
  intro x _
  exact hle (hb.2.symm ▸ Submodule.mem_top)

/-- p 乗部分体上の導分は p-basis 上の値で決まる。 -/
theorem derivation_ext
    {V : Type*} [AddCommGroup V] [Module K V] [Module (pPowerSubfield K p) V]
    (hb : IsPBasis K p b)
    {δ ε : Derivation (pPowerSubfield K p) K V} (h : ∀ i, δ (b i) = ε (b i)) :
    δ = ε := by
  apply Derivation.ext_of_adjoin_eq_top (Set.range b) hb.adjoin_eq_top
  rintro _ ⟨i, rfl⟩
  exact h i

end IsPBasis

/-- 空の p-basis は、p 乗部分体が全体であることと同値。 -/
theorem isPBasis_empty_iff {ι : Type*} [IsEmpty ι] (b : ι → K) :
    IsPBasis K p b ↔ pPowerSubfield K p = ⊤ := by
  classical
  have hz (d : PExponent p ι) : d = 0 := by
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    exact isEmptyElim i
  let : Unique (PExponent p ι) := ⟨⟨0⟩, hz⟩
  have hmono : pMonomial (p := p) b = fun _ ↦ (1 : K) := by
    funext d
    rw [hz d, pMonomial_zero]
  have hli : LinearIndependent (pPowerSubfield K p) (pMonomial (p := p) b) := by
    rw [linearIndependent_unique_iff, hmono]
    exact one_ne_zero
  constructor
  · intro hb
    apply top_le_iff.mp
    intro x _
    have hx : x ∈ Submodule.span (pPowerSubfield K p) ({1} : Set K) := by
      have hr : Set.range (pMonomial (p := p) b) = {1} := by simp [hmono]
      rw [← hr, hb.2]
      trivial
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
    have hcx : (c : K) = x := by
      change (c : K) * 1 = x at hc
      simpa using hc
    exact hcx ▸ c.property
  · intro htop
    refine ⟨hli, top_le_iff.mp ?_⟩
    intro x _
    have hx : x ∈ pPowerSubfield K p := by rw [htop]; trivial
    have h1 : (1 : K) ∈ Submodule.span (pPowerSubfield K p)
        (Set.range (pMonomial (p := p) b)) :=
      Submodule.subset_span ⟨0, pMonomial_zero b⟩
    have h := Submodule.smul_mem _ (⟨x, hx⟩ : pPowerSubfield K p) h1
    change x * 1 ∈ _ at h
    simpa using h

theorem isPBasis_empty_of_perfect [PerfectField K] {ι : Type*} [IsEmpty ι] (b : ι → K) :
    IsPBasis K p b := (isPBasis_empty_iff K p b).mpr (pPowerSubfield_eq_top_of_perfect K p)

end SerrePositivity
