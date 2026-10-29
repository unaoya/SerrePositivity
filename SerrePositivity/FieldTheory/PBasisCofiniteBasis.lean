module

public import SerrePositivity.FieldTheory.PBasisCofiniteField
public import SerrePositivity.FieldTheory.PMonomialPartition
public import SerrePositivity.LinearAlgebra.BasisScalarIndependence
public import Mathlib.Algebra.Group.Submonoid.Finsupp

/-! # 有限方向の中間係数体上の相対単項式基底

補集合の単項式を係数の基底として展開し、元のp-basisの独立性へ戻す。
生成性は添加の単項式をp未満の指数に還元して得る。
-/

@[expose] public noncomputable section
namespace SerrePositivity
variable {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
  {ι : Type*} {b : ι → K}

/-- 補集合の単項式は中間係数体自身のp乗部分体上の基底。 -/
def IsPBasis.cofiniteCoefficientBasis (hb : IsPBasis K p b) (e : Finset ι) :
    Module.Basis (PExponent p {i : ι // i ∉ e}) (pPowerSubfield K p)
      (pBasisCofiniteField (p := p) b e) := by
  have hli : LinearIndependent (pPowerSubfield K p)
      (pMonomial (p := p) (fun i : {i : ι // i ∉ e} ↦ b i)) :=
    hb.linearIndependent_comp (Function.Embedding.subtype (· ∉ e))
  exact Module.Basis.span hli

@[simp] theorem IsPBasis.cofiniteCoefficientBasis_apply_coe (hb : IsPBasis K p b)
    (e : Finset ι) (d : PExponent p {i : ι // i ∉ e}) :
    (hb.cofiniteCoefficientBasis e d : K) = pMonomial (fun i : {i : ι // i ∉ e} ↦ b i) d := by
  unfold IsPBasis.cofiniteCoefficientBasis
  exact Module.Basis.coe_span_apply _ d

/-- 残した方向の単項式は、中間係数体上でも独立。 -/
theorem IsPBasis.linearIndependent_cofiniteMonomials (hb : IsPBasis K p b) (e : Finset ι) :
    LinearIndependent (pBasisCofiniteField (p := p) b e)
      (pMonomial (p := p) (fun i : e ↦ b i)) := by
  classical
  let B := hb.cofiniteCoefficientBasis e
  apply linearIndependent_of_smul_of_span_eq_top B.span_eq
  rw [← linearIndependent_equiv' (.prodComm ..)
    (g := fun z : PExponent p e × PExponent p {i : ι // i ∉ e} ↦
      B z.2 • pMonomial (fun i : e ↦ b i) z.1) rfl]
  have h := hb.1.comp (PExponent.combinePartition (e : Set ι))
    (PExponent.combinePartition_injective (p := p) (e : Set ι))
  have he : (fun z : PExponent p e × PExponent p {i : ι // i ∉ e} ↦
      B z.2 • pMonomial (fun i : e ↦ b i) z.1) =
        fun z ↦ pMonomial b (PExponent.combinePartition (e : Set ι) z) := by
    funext z
    change (B z.2 : K) * pMonomial (fun i : e ↦ b i) z.1 = _
    rw [IsPBasis.cofiniteCoefficientBasis_apply_coe, pMonomial_combinePartition]
    exact mul_comm _ _
  rw [he]
  exact h

/-- 中間係数体上では、p未満の有限個の指数の単項式で全体を生成する。 -/
theorem IsPBasis.span_cofiniteMonomials (hb : IsPBasis K p b) (e : Finset ι) :
    Submodule.span (pBasisCofiniteField (p := p) b e)
      (Set.range (pMonomial (p := p) (fun i : e ↦ b i))) = ⊤ := by
  classical
  let E := pBasisCofiniteField (p := p) b e
  let v := fun i : e ↦ b i
  let V := Submodule.span E (Set.range (pMonomial (p := p) v))
  have hle : (Algebra.adjoin E (Set.range v)).toSubmodule ≤ V := by
    rw [Algebra.adjoin_eq_span]
    apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨d, rfl⟩ := Submonoid.exists_finsupp_of_mem_closure_range v x hx
    rw [finsuppMonomial_eq_pow_mul_remainder p v d]
    let c : E := ⟨(d.prod (fun i n ↦ v i ^ (n / p))) ^ p, E.algebraMap_mem
      ⟨_, (mem_pPowerSubfield K p _).mpr ⟨_, rfl⟩⟩⟩
    exact V.smul_mem c (Submodule.subset_span ⟨PExponent.remainder p d, rfl⟩)
  rw [hb.adjoin_cofiniteField_eq_top e] at hle
  exact top_le_iff.mp hle

/-- κ/κ_eの実際の相対単項式基底。 -/
def IsPBasis.cofiniteMonomialBasis (hb : IsPBasis K p b) (e : Finset ι) :
    Module.Basis (PExponent p e) (pBasisCofiniteField (p := p) b e) K :=
  Module.Basis.mk (hb.linearIndependent_cofiniteMonomials e)
    (by rw [hb.span_cofiniteMonomials e])

@[simp] theorem IsPBasis.cofiniteMonomialBasis_apply (hb : IsPBasis K p b)
    (e : Finset ι) (d : PExponent p e) :
    hb.cofiniteMonomialBasis e d = pMonomial (fun i : e ↦ b i) d :=
  Module.Basis.mk_apply _ _ _

/-- 残した方向の個数から、拡大次数を正確に計算する。 -/
theorem IsPBasis.finrank_cofiniteField (hb : IsPBasis K p b) (e : Finset ι) :
    Module.finrank (pBasisCofiniteField (p := p) b e) K = p ^ e.card := by
  classical
  rw [Module.finrank_eq_card_basis (hb.cofiniteMonomialBasis e), PExponent.card,
    Fintype.card_coe]

/-- 中間係数体上の単項式展開は有限台で一意。 -/
theorem IsPBasis.existsUnique_cofiniteExpansion (hb : IsPBasis K p b) (e : Finset ι) (x : K) :
    ∃! c : PExponent p e →₀ pBasisCofiniteField (p := p) b e,
      c.sum (fun d a ↦ (a : K) * pMonomial (fun i : e ↦ b i) d) = x := by
  let B := hb.cofiniteMonomialBasis e
  have hs (c : PExponent p e →₀ pBasisCofiniteField (p := p) b e) :
      c.sum (fun d a ↦ (a : K) * pMonomial (fun i : e ↦ b i) d) = B.repr.symm c := by
    rw [Module.Basis.repr_symm_apply, Finsupp.linearCombination_apply]
    apply Finsupp.sum_congr
    intro d _
    rw [IsPBasis.cofiniteMonomialBasis_apply]
    rfl
  refine ⟨B.repr x, (hs (B.repr x)).trans (B.repr.symm_apply_apply x), ?_⟩
  intro c hc
  apply B.repr.symm.injective
  exact (hs c).symm.trans (hc.trans (B.repr.symm_apply_apply x).symm)

end SerrePositivity
