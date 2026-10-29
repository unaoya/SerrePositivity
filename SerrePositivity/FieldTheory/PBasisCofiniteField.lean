module

public import SerrePositivity.FieldTheory.PMonomialSpan
public import SerrePositivity.LinearAlgebra.BasisScalarIndependence

/-! # p 基底の有限個の方向を残す中間係数体

概要：`b` を標数 `p` の体 `K` の p 基底、`e` を添字の有限集合とする。`e` の外の基底元を `K^p` に
添加した中間体を `K_e`（`pBasisCofiniteField`）と書く。
- `K_e` に `e` の基底元を添加すると `K` 全体になる。`i ∈ e` なら `b i ∉ K_e`。
- `K_e` の元の単項式座標は、`e` の方向を使う指数では零。`K_e` 全体の交わりは `K^p`。
- 補集合の単項式は `K_e` の `K^p` 上の基底、`e` の単項式は `K` の `K_e` 上の基底。
  特に `K/K_e` は有限で、`[K : K_e] = p^{|e|}`。
方針：`K_e` の元は補集合の単項式の `K^p` 上の線形包に属する（`PMonomialSpan`）ので、座標の議論は
p 基底の単項式基底で行う。`K/K_e` の生成性は相対版の `span_pMonomial_eq_adjoin_of_pow_mem` から、
独立性は二つの単項式族の積が元の p 基底の単項式になること（`pMonomial_combinePartition`）から従う。
規約：p 基底の添字集合の有限性は仮定しない。一方向を除いた中間体は `e = {i}` の場合として扱う。
使われ方：Cohen–Gabber 型の係数体と共有限な係数の議論（CommutativeAlgebra の `Cofinite*`）、
`K^p` 上の微分の零判定（`ExponentOneDifferentialConstants`）。
-/

@[expose] public noncomputable section
namespace SerrePositivity

variable {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
  {ι : Type*} (b : ι → K)

section Field

/-- `e` の外の p 基底元を `K^p` に添加した中間体 `K_e`。 -/
def pBasisCofiniteField (e : Finset ι) : IntermediateField (pPowerSubfield K p) K :=
  IntermediateField.adjoin (pPowerSubfield K p) (Set.range fun j : {j : ι // j ∉ e} ↦ b j)

theorem mem_pBasisCofiniteField (e : Finset ι) {i : ι} (hi : i ∉ e) :
    b i ∈ pBasisCofiniteField (p := p) b e :=
  IntermediateField.subset_adjoin _ _ ⟨⟨i, hi⟩, rfl⟩

/-- 残す方向を増やすと、係数体は小さくなる。 -/
theorem pBasisCofiniteField_antitone {e f : Finset ι} (hef : e ⊆ f) :
    pBasisCofiniteField (p := p) b f ≤ pBasisCofiniteField (p := p) b e := by
  apply IntermediateField.adjoin.mono
  rintro _ ⟨j, rfl⟩
  exact ⟨⟨j, fun hj ↦ j.property (hef hj)⟩, rfl⟩

variable {b}

/-- 残した有限個の元を中間係数体へ添加すれば、元の体全体になる。 -/
theorem IsPBasis.adjoin_cofiniteField_eq_top (hb : IsPBasis K p b) (e : Finset ι) :
    Algebra.adjoin (pBasisCofiniteField (p := p) b e)
      (Set.range (fun j : e ↦ b j)) = ⊤ := by
  classical
  let E := pBasisCofiniteField (p := p) b e
  let A := Algebra.adjoin E (Set.range (fun j : e ↦ b j))
  have hle : Algebra.adjoin (pPowerSubfield K p) (Set.range b) ≤
      A.restrictScalars (pPowerSubfield K p) := by
    apply Algebra.adjoin_le
    rintro _ ⟨j, rfl⟩
    change b j ∈ A
    by_cases hj : j ∈ e
    · exact Algebra.subset_adjoin ⟨⟨j, hj⟩, rfl⟩
    · exact A.algebraMap_mem (⟨b j, mem_pBasisCofiniteField b e hj⟩ : E)
  apply top_le_iff.mp
  intro x _
  exact hle (hb.adjoin_eq_top.symm ▸ Algebra.mem_top)

/-- 一方向だけを残す場合：`K_{i}` に `b i` を添加すれば全体。 -/
theorem IsPBasis.adjoin_cofiniteField_singleton_eq_top (hb : IsPBasis K p b)
    (i : ι) : Algebra.adjoin (pBasisCofiniteField (p := p) b {i}) {b i} = ⊤ := by
  have h := hb.adjoin_cofiniteField_eq_top {i}
  have hr : Set.range (fun j : ({i} : Finset ι) ↦ b j) = {b i} := by
    ext x
    constructor
    · rintro ⟨⟨j, hj⟩, rfl⟩
      obtain rfl := Finset.mem_singleton.mp hj
      rfl
    · rintro rfl
      exact ⟨⟨i, Finset.mem_singleton_self i⟩, rfl⟩
  rwa [hr] at h

end Field

section Coord

variable {b}

/-- `K_e` の元の単項式座標は、`e` の方向を使う指数では零。 -/
theorem IsPBasis.coord_eq_zero_of_mem_cofiniteField (hb : IsPBasis K p b)
    (e : Finset ι) (d : PExponent p ι) (hd : ∃ i ∈ e, d.val i ≠ 0)
    {x : K} (hx : x ∈ pBasisCofiniteField (p := p) b e) : hb.basis.coord d x = 0 := by
  classical
  obtain ⟨i, hie, hdi⟩ := hd
  let emb : {j : ι // j ∉ e} ↪ ι := Function.Embedding.subtype (· ∉ e)
  let c := hb.basis.coord d
  have hc : Submodule.span (pPowerSubfield K p) (Set.range (pMonomial (p := p) (b ∘ emb))) ≤
      LinearMap.ker c := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    have hne : PExponent.embDomain emb a ≠ d := by
      intro h
      have hv := congrArg (fun z : PExponent p ι ↦ z.val i) h
      change a.val.embDomain emb i = d.val i at hv
      rw [Finsupp.embDomain_of_notMem_range _ _ _ (by rintro ⟨j, rfl⟩; exact j.property hie)]
        at hv
      exact hdi hv.symm
    change c (pMonomial (b ∘ emb) a) = 0
    rw [← pMonomial_embDomain b emb a, ← hb.basis_apply (PExponent.embDomain emb a)]
    simp only [c, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    exact ite_eq_right hne
  exact hc ((mem_adjoin_pPowerSubfield_iff_mem_span_pMonomial (b ∘ emb)).mp hx)

/-- 残した方向の基底元は `K_e` に属さない。 -/
theorem IsPBasis.notMem_cofiniteField (hb : IsPBasis K p b) {e : Finset ι} {i : ι}
    (hi : i ∈ e) : b i ∉ pBasisCofiniteField (p := p) b e := by
  classical
  intro h
  let n : Fin p := ⟨1, (Fact.out : p.Prime).one_lt⟩
  let d0 : PExponent p ι := PExponent.single i n
  have hci : hb.basis.coord d0 (b i) = 1 := by
    have heq : pMonomial b d0 = b i := by simp [d0, n]
    rw [← heq, ← hb.basis_apply d0]
    simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]
  have hz := hb.coord_eq_zero_of_mem_cofiniteField e d0
    ⟨i, hi, by simp [d0, PExponent.single, n]⟩ h
  exact one_ne_zero (hci.symm.trans hz)

/-- 全ての有限集合に対する中間係数体の交わりは、p乗部分体そのもの。 -/
theorem IsPBasis.iInf_cofiniteField_eq_bot (hb : IsPBasis K p b) :
    (⨅ e : Finset ι, pBasisCofiniteField (p := p) b e) = ⊥ := by
  classical
  apply le_antisymm ?_ bot_le
  intro x hx
  have hxe (e : Finset ι) : x ∈ pBasisCofiniteField (p := p) b e :=
    (iInf_le (fun e ↦ pBasisCofiniteField (p := p) b e) e) hx
  let a := hb.basis.repr x 0
  apply IntermediateField.mem_bot.mpr
  refine ⟨a, ?_⟩
  change (a : K) = x
  symm
  apply hb.basis.repr.injective
  have ha : (a : K) = a • hb.basis 0 := by
    rw [hb.basis_apply, pMonomial_zero]
    change (a : K) = (a : K) * 1
    exact (mul_one _).symm
  rw [ha, map_smul, hb.basis.repr_self]
  ext d
  by_cases hd : d = 0
  · subst d
    simp [a]
  · have hex : ∃ i, d.val i ≠ 0 := by
      by_contra hh
      apply hd
      apply Subtype.ext
      ext i
      by_contra hi
      exact hh ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hex
    have hc := hb.coord_eq_zero_of_mem_cofiniteField {i} d ⟨i, by simp, hi⟩ (hxe {i})
    simpa [Module.Basis.coord_apply, Finsupp.smul_apply, Finsupp.single_apply, hd, Ne.symm hd]
      using hc

end Coord

section Basis

variable {b}

/-- 補集合の単項式は中間係数体自身のp乗部分体上の基底。 -/
def IsPBasis.cofiniteCoefficientBasis (hb : IsPBasis K p b) (e : Finset ι) :
    Module.Basis (PExponent p {i : ι // i ∉ e}) (pPowerSubfield K p)
      (pBasisCofiniteField (p := p) b e) := by
  have hli : LinearIndependent (pPowerSubfield K p)
      (pMonomial (p := p) (fun i : {i : ι // i ∉ e} ↦ b i)) :=
    hb.linearIndependent_comp (Function.Embedding.subtype (· ∉ e))
  exact (Module.Basis.span hli).map (LinearEquiv.ofEq _ _
    (adjoin_pPowerSubfield_toSubmodule_eq_span_pMonomial _).symm)

@[simp] theorem IsPBasis.cofiniteCoefficientBasis_apply_coe (hb : IsPBasis K p b)
    (e : Finset ι) (d : PExponent p {i : ι // i ∉ e}) :
    (hb.cofiniteCoefficientBasis e d : K) = pMonomial (fun i : {i : ι // i ∉ e} ↦ b i) d := by
  unfold IsPBasis.cofiniteCoefficientBasis
  exact Module.Basis.coe_span_apply
    (hb.linearIndependent_comp (Function.Embedding.subtype (· ∉ e))) d

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

/-- `e` の単項式は `K_e` 上で `K` を張る。相対版の p 単項式の線形包と添加の同定から従う。 -/
theorem IsPBasis.span_cofiniteMonomials (hb : IsPBasis K p b) (e : Finset ι) :
    Submodule.span (pBasisCofiniteField (p := p) b e)
      (Set.range (pMonomial (p := p) (fun i : e ↦ b i))) = ⊤ := by
  let E := pBasisCofiniteField (p := p) b e
  refine (span_pMonomial_eq_adjoin_of_pow_mem (F := E) (p := p) (fun i : e ↦ b i) fun j ↦
      ⟨⟨b j ^ p, E.algebraMap_mem ⟨b j ^ p, (mem_pPowerSubfield K p _).mpr ⟨b j, rfl⟩⟩⟩, rfl⟩).trans
    ?_
  rw [hb.adjoin_cofiniteField_eq_top e, Algebra.top_toSubmodule]

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

/-- 有限個の方向を残す拡大は有限。 -/
theorem IsPBasis.finite_cofiniteField (hb : IsPBasis K p b) (e : Finset ι) :
    Module.Finite (pBasisCofiniteField (p := p) b e) K :=
  Module.Finite.of_basis (hb.cofiniteMonomialBasis e)

end Basis

end SerrePositivity
