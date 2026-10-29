module

public import SerrePositivity.FieldTheory.PMonomialSpan
public import Mathlib.Order.TeichmullerTukey
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.Logic.Equiv.Option

/-! # p 独立集合と p 基底の存在

概要：標数 `p` の体 `K` の部分集合 `s` が p 独立とは、`s` の元の p 単項式が `K^p` 上独立であること。
- 任意の p 独立集合は p 基底に延長できる。特に任意の体は p 基底を持つ（有限 p 次数は不要）。
- `K^p` に属さない元を含む p 基底が存在する。
方針：`s` を添字とする族のままでは集合の包含で比べにくいので、`K` 自身を共通の添字にして
「台が `s` に含まれる p 指数の上での独立性」（`IsPIndependentSet`）として定義する。
すると独立性は有限部分集合で検査でき（Mathlib の `linearIndepOn_of_finite`）、有限性原理
（Teichmüller–Tukey）で極大な p 独立集合が得られる。極大な集合は全体を生成する。生成中間体の外の元
`x` を添加すると、中間体上の `x` の冪の独立性と Mathlib の `linearIndependent_smul` から独立性が
保たれ、極大性に反するからである。
規約：集合版と族版（`s` を添字とする p 単項式の独立性）の同値は `isPIndependentSet_iff_linearIndependent`。
使われ方：p 基底の存在（Cohen–Gabber の微分パラメータ・係数体）、`K^p` 上の微分の零判定
（`ExponentOneDifferentialConstants`）。
-/

@[expose] public section
namespace SerrePositivity

variable {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]

/-- 台が指定集合に含まれる p 指数。 -/
def supportedPExponents (s : Set K) : Set (PExponent p K) :=
  {d | ∀ x ∈ d.val.support, x ∈ s}

/-- 元の体を共通添字として記述した p 独立集合。 -/
def IsPIndependentSet (s : Set K) : Prop :=
  LinearIndepOn (pPowerSubfield K p) (pMonomial (p := p) (id : K → K))
    (supportedPExponents (p := p) s)

omit [Field K] [Fact p.Prime] [CharP K p] in
theorem supportedPExponents_mono {s t : Set K} (h : s ⊆ t) :
    supportedPExponents (p := p) s ⊆ supportedPExponents (p := p) t :=
  fun _ hd x hx ↦ h (hd x hx)

theorem IsPIndependentSet.mono {s t : Set K} (ht : IsPIndependentSet (p := p) t)
    (h : s ⊆ t) : IsPIndependentSet (p := p) s :=
  LinearIndepOn.mono ht (supportedPExponents_mono h)

omit [Field K] [Fact p.Prime] [CharP K p] in
/-- 有限個の指数は有限個の変数だけを使う。 -/
theorem exists_finite_support_set {s : Set K} {u : Set (PExponent p K)} (hu : u.Finite)
    (hus : u ⊆ supportedPExponents (p := p) s) :
    ∃ t ⊆ s, t.Finite ∧ u ⊆ supportedPExponents (p := p) t :=
  ⟨⋃ d ∈ u, (d.val.support : Set K), Set.iUnion₂_subset fun _ hd x hx ↦ hus hd x hx,
    hu.biUnion fun d _ ↦ d.val.support.finite_toSet,
    fun d hd _ hx ↦ Set.mem_iUnion₂.mpr ⟨d, hd, hx⟩⟩

/-- p 独立性は全ての有限部分集合で検査できる。 -/
theorem isPIndependentSet_iff_finite (s : Set K) :
    IsPIndependentSet (p := p) s ↔
      ∀ t ⊆ s, t.Finite → IsPIndependentSet (p := p) t := by
  refine ⟨fun hs t hts _ ↦ hs.mono hts, fun h ↦ linearIndepOn_of_finite _ fun u hus hu ↦ ?_⟩
  obtain ⟨t, hts, ht, hut⟩ := exists_finite_support_set hu hus
  exact LinearIndepOn.mono (h t hts ht) hut

/-- 任意の p 独立集合を包含する最大 p 独立集合が存在する。 -/
theorem exists_maximal_pIndependentSet (s : Set K) (hs : IsPIndependentSet (p := p) s) :
    ∃ t, s ⊆ t ∧ Maximal (IsPIndependentSet (p := p)) t := by
  exact (show Order.IsOfFiniteCharacter {t : Set K | IsPIndependentSet (p := p) t} from
    isPIndependentSet_iff_finite).exists_maximal hs

omit [Field K] [CharP K p] in
/-- 指定集合に台を持つ指数は、その集合を添字とする指数の零延長に一致する。 -/
theorem supportedPExponents_eq_range (s : Set K) :
    supportedPExponents (p := p) s =
      Set.range (PExponent.embDomain (p := p) (Function.Embedding.subtype (· ∈ s))) := by
  ext d
  have h := Finsupp.mem_range_embDomain_iff (Function.Embedding.subtype (· ∈ s)) d.val
  rw [Function.Embedding.coe_subtype, Subtype.range_coe] at h
  constructor
  · intro hd
    obtain ⟨e, he⟩ := h.mpr fun x hx ↦ hd x hx
    refine ⟨⟨e, fun i ↦ ?_⟩, Subtype.ext he⟩
    have hi := d.property i
    rw [← he] at hi
    change Finsupp.embDomain (Function.Embedding.subtype (· ∈ s)) e
      (Function.Embedding.subtype (· ∈ s) i) < p at hi
    rwa [Finsupp.embDomain_apply_self] at hi
  · rintro ⟨e, rfl⟩
    exact fun x hx ↦ h.mp ⟨e.val, rfl⟩ hx

/-- 共通添字による集合版と、元の集合を添字とする単項式族の独立性との同値。 -/
theorem isPIndependentSet_iff_linearIndependent (s : Set K) :
    IsPIndependentSet (p := p) s ↔
      LinearIndependent (pPowerSubfield K p) (pMonomial (p := p) (Subtype.val : s → K)) := by
  rw [IsPIndependentSet, supportedPExponents_eq_range,
    linearIndepOn_range_iff (PExponent.embDomain_injective _)]
  simp only [Function.comp_def, pMonomial_embDomain]
  rfl

/-- 独立な p 単項式族に、その生成する中間体の外の元を一つ添加しても独立。
中間体上で添加する元の冪が独立なので、Mathlib のスカラー塔の独立性（`linearIndependent_smul`）から
単項式と冪の積が独立になる。 -/
theorem linearIndependent_pMonomial_optionElim
    {ι : Type*} (b : ι → K)
    (hb : LinearIndependent (pPowerSubfield K p) (pMonomial (p := p) b))
    (x : K) (hx : x ∉ IntermediateField.adjoin (pPowerSubfield K p) (Set.range b)) :
    LinearIndependent (pPowerSubfield K p) (pMonomial (p := p) (Option.elim' x b)) := by
  let E := IntermediateField.adjoin (pPowerSubfield K p) (Set.range b)
  let v : PExponent p ι → E := fun d ↦
    ⟨pMonomial b d, (mem_adjoin_pPowerSubfield_iff_mem_span_pMonomial b).mpr
      (Submodule.subset_span ⟨d, rfl⟩)⟩
  have hbE : LinearIndependent (pPowerSubfield K p) v :=
    LinearIndependent.of_comp E.val.toLinearMap hb
  let a : E := ⟨x ^ p, E.algebraMap_mem ⟨x ^ p, (mem_pPowerSubfield K p _).mpr ⟨x, rfl⟩⟩⟩
  have hpow : LinearIndependent E (fun i : Fin p ↦ x ^ (i : ℕ)) :=
    linearIndependent_pow_of_prime_pow_eq x a rfl fun ⟨y, hy⟩ ↦ hx (hy ▸ y.property)
  have hmul : LinearIndependent (pPowerSubfield K p)
      (fun i : PExponent p ι × Fin p ↦ pMonomial b i.1 * x ^ (i.2 : ℕ)) := by
    convert linearIndependent_smul hbE hpow using 1
  have h := hmul.comp PExponent.splitOption PExponent.splitOption_injective
  change LinearIndependent (pPowerSubfield K p) (fun d ↦ pMonomial (Option.elim' x b) d)
  simpa only [Function.comp_def, pMonomial_optionElim] using h

/-- 生成中間体の外の元を集合へ添加しても p 独立性を保つ。 -/
theorem IsPIndependentSet.insert {s : Set K} (hs : IsPIndependentSet (p := p) s)
    (x : K) (hx : x ∉ IntermediateField.adjoin (pPowerSubfield K p)
      (Set.range (Subtype.val : s → K))) :
    IsPIndependentSet (p := p) (Insert.insert x s) := by
  classical
  have hxS : x ∉ s := fun h ↦ hx (IntermediateField.subset_adjoin _ _ ⟨⟨x, h⟩, rfl⟩)
  let e : Option s ≃ (Insert.insert x s : Set K) :=
    (Equiv.optionEquivSumPUnit s).trans (Equiv.Set.insert hxS).symm
  have hf (z : Option s) : (e z : K) = Option.elim' x Subtype.val z := by
    cases z <;> simp [e]
  have heq : Option.elim' x (Subtype.val : s → K) ∘ e.symm = Subtype.val := by
    funext y
    simpa using (hf (e.symm y)).symm
  apply (isPIndependentSet_iff_linearIndependent _).mpr
  have hind := linearIndependent_pMonomial_optionElim (Subtype.val : s → K)
    ((isPIndependentSet_iff_linearIndependent s).mp hs) x hx
  have h := linearIndependent_pMonomial_comp hind e.symm.toEmbedding
  change LinearIndependent (pPowerSubfield K p)
    (pMonomial (p := p) (Option.elim' x (Subtype.val : s → K) ∘ e.symm)) at h
  rw [heq] at h
  exact h

/-- 最大 p 独立集合は全体を生成し、p-basis になる。 -/
theorem maximal_pIndependentSet_isPBasis {s : Set K}
    (hs : Maximal (IsPIndependentSet (p := p)) s) :
    IsPBasis K p (Subtype.val : s → K) := by
  refine ⟨(isPIndependentSet_iff_linearIndependent s).mp hs.prop, ?_⟩
  apply top_le_iff.mp
  intro x _
  by_contra hx
  have hx' : x ∉ IntermediateField.adjoin (pPowerSubfield K p)
      (Set.range (Subtype.val : s → K)) :=
    (mem_adjoin_pPowerSubfield_iff_mem_span_pMonomial _).not.mpr hx
  have hxS := hs.mem_of_prop_insert (hs.prop.insert x hx')
  exact hx' (IntermediateField.subset_adjoin _ _ ⟨⟨x, hxS⟩, rfl⟩)

/-- 任意の p 独立集合は p-basis に拡張できる。 -/
theorem exists_pBasis_superset (s : Set K) (hs : IsPIndependentSet (p := p) s) :
    ∃ t : Set K, s ⊆ t ∧ IsPBasis K p (Subtype.val : t → K) := by
  obtain ⟨t, hst, ht⟩ := exists_maximal_pIndependentSet s hs
  exact ⟨t, hst, maximal_pIndependentSet_isPBasis ht⟩

/-- 空集合はp独立。p-basisの存在と指定した元の添加に共通して使う。 -/
theorem isPIndependentSet_empty : IsPIndependentSet (p := p) (∅ : Set K) := by
  have hzero (d : PExponent p (∅ : Set K)) : d = 0 := by
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    exact i.property.elim
  let : Unique (PExponent p (∅ : Set K)) := ⟨⟨0⟩, hzero⟩
  rw [isPIndependentSet_iff_linearIndependent, linearIndependent_unique_iff]
  change pMonomial (Subtype.val : (∅ : Set K) → K) (0 : PExponent p (∅ : Set K)) ≠ 0
  rw [pMonomial_zero]
  exact one_ne_zero

/-- 任意の標数 p の体は p-basis を持つ。有限 p-rank・完全体性は不要。 -/
theorem exists_pBasis : ∃ s : Set K, IsPBasis K p (Subtype.val : s → K) := by
  obtain ⟨s, _, hb⟩ := exists_pBasis_superset (∅ : Set K) isPIndependentSet_empty
  exact ⟨s, hb⟩

/-- p 乗でない元を含む p 基底が存在する。 -/
theorem exists_pBasis_containing_of_not_mem_pPowerSubfield (x : K)
    (hx : x ∉ pPowerSubfield K p) :
    ∃ s : Set K, x ∈ s ∧ IsPBasis K p (Subtype.val : s → K) := by
  have hxe : x ∉ IntermediateField.adjoin (pPowerSubfield K p)
      (Set.range (Subtype.val : (∅ : Set K) → K)) := by
    rw [Set.range_eq_empty, IntermediateField.adjoin_empty]
    intro h
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp h
    exact hx (hc ▸ c.property)
  obtain ⟨s, hsub, hb⟩ := exists_pBasis_superset _ (isPIndependentSet_empty.insert x hxe)
  exact ⟨s, hsub (by simp), hb⟩

end SerrePositivity
