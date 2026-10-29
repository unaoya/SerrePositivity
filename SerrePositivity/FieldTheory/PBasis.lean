module

public import SerrePositivity.FieldTheory.PExponent
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.AlgebraTower
public import SerrePositivity.LinearAlgebra.BasisRingEquiv

/-! # p 乗部分体と p 基底

概要：正標数 `p` の体 `K` の p 乗部分体 `K^p`（Frobenius の像）と、p 基底（p 単項式が `K^p` 上の基底になる族）。
- p 乗部分体：Frobenius との同型、体の準同型による像、体同型が誘導する同型。
- p 基底：線形代数の基底と p 乗根の係数による展開、次数、代数としての生成、導分と環準同型の一意性、
  体同型による移送、空の p 基底の判定。
方針：p 乗部分体は Mathlib の `(frobenius K p).fieldRange`、同型は `rangeRestrictFieldEquiv` で定義する。
規約：存在定理（`PIndependentSet`）や相対版（`RelativePMonomialSpan`・`PBasisDifferentials`）は別の場所に置く。
使われ方：FieldTheory の p 基底の理論全体と Cohen–Gabber の正規化。Mathlib への提出候補（mathlib-upstream の G1）。
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

section Map

variable {K L : Type*} [Field K] [Field L] {p : ℕ} [Fact p.Prime] [CharP K p] [CharP L p]

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

end Map

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

section Transport

variable {k l : Type*} [Field k] [Field l] {p : ℕ} [Fact p.Prime]
  [CharP k p] [CharP l p]

/-- 体同型が誘導する p 乗部分体の同型。 -/
noncomputable def pPowerSubfieldEquiv (e : k ≃+* l) :
    pPowerSubfield k p ≃+* pPowerSubfield l p :=
  (pPowerEquiv k p).symm.trans (e.trans (pPowerEquiv l p))

@[simp] theorem pPowerSubfieldEquiv_apply_coe (e : k ≃+* l)
    (c : pPowerSubfield k p) : (pPowerSubfieldEquiv e c : l) = e (c : k) := by
  change (e ((pPowerEquiv k p).symm c)) ^ p = e (c : k)
  rw [← map_pow]
  congr 1
  exact congrArg Subtype.val ((pPowerEquiv k p).apply_symm_apply c)

/-- p-basis の独立性と生成性は、ともに体同型で保たれる。 -/
theorem IsPBasis.ringEquiv {ι : Type*} {b : ι → k} (hb : IsPBasis k p b)
    (e : k ≃+* l) : IsPBasis l p (e ∘ b) := by
  let B := basisOfRingEquiv hb.basis (pPowerSubfieldEquiv e) e
    (fun c ↦ (pPowerSubfieldEquiv_apply_coe e c).symm)
  have he : ∀ d : PExponent p ι, B d = pMonomial (e ∘ b) d := by
    intro d
    rw [show B d = e (hb.basis d) from basisOfRingEquiv_apply _ _ _ _ d, hb.basis_apply]
    simp only [pMonomial, map_finsuppProd, map_pow, Function.comp_apply]
  have hfun : (B : PExponent p ι → l) = pMonomial (e ∘ b) := funext he
  exact ⟨hfun ▸ B.linearIndependent, hfun ▸ B.span_eq⟩

end Transport

section RingHomExt

variable {k A : Type*} [Field k] [CommRing A]
variable {p : ℕ} [Fact p.Prime] [CharP k p]
variable {ι : Type*} {b : ι → k}

/-- p-basis と全ての p 乗で一致する環写像は一致する。 -/
theorem IsPBasis.ringHom_ext_of_eq_pow (hb : IsPBasis k p b)
    (l₁ l₂ : k →+* A) (hbmap : ∀ i, l₁ (b i) = l₂ (b i))
    (hpow : ∀ x, l₁ (x ^ p) = l₂ (x ^ p)) : l₁ = l₂ := by
  classical
  have hmono (d : PExponent p ι) : l₁ (pMonomial b d) = l₂ (pMonomial b d) := by
    simp only [pMonomial, Finsupp.prod, map_prod, map_pow, hbmap]
  ext x
  rw [← hb.sum_expansionEquiv x]
  simp only [Finsupp.sum, map_sum, map_mul, hpow, hmono]

/-- p-basis と、一つの Frobenius 冪の像で一致すれば、写像全体が一致する。 -/
theorem IsPBasis.ringHom_ext_of_eq_pow_exp (hb : IsPBasis k p b)
    (l₁ l₂ : k →+* A) (hbmap : ∀ i, l₁ (b i) = l₂ (b i))
    (n : ℕ) (hpow : ∀ x, l₁ (x ^ p ^ n) = l₂ (x ^ p ^ n)) : l₁ = l₂ := by
  induction n with
  | zero =>
    ext x
    simpa using hpow x
  | succ n ih =>
    let m₁ := l₁.comp (iterateFrobenius k p n)
    let m₂ := l₂.comp (iterateFrobenius k p n)
    have hm : m₁ = m₂ := by
      apply hb.ringHom_ext_of_eq_pow
      · intro i
        change l₁ ((b i) ^ p ^ n) = l₂ ((b i) ^ p ^ n)
        simp only [map_pow, hbmap]
      · intro x
        change l₁ ((x ^ p) ^ p ^ n) = l₂ ((x ^ p) ^ p ^ n)
        simpa only [← pow_mul, Nat.pow_succ, Nat.mul_comm] using hpow x
    apply ih
    intro x
    exact RingHom.congr_fun hm x

end RingHomExt

end SerrePositivity
