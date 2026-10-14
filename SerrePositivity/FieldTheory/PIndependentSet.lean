module

public import SerrePositivity.FieldTheory.PAdjoin
public import Mathlib.Order.TeichmullerTukey
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.Logic.Equiv.Option

/-! # p 独立集合の有限性原理

指数の台を元の体内で指定し、有限個の単項式に関する関係を
有限個の変数へ制限する。最大独立集合の存在には Mathlib の
有限性原理（Zorn の補題による Teichmüller–Tukey）を使う。
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
/-- 有限個の単項式は有限個の変数だけを使う。 -/
theorem exists_finite_support_set
    (t : Set (PExponent p K)) (ht : t.Finite) :
    ∃ s : Set K, s.Finite ∧ t ⊆ supportedPExponents (p := p) s := by
  refine ⟨⋃ d ∈ t, (d.val.support : Set K),
    ht.biUnion (fun d _ ↦ d.val.support.finite_toSet), ?_⟩
  intro d hd x hx
  exact Set.mem_iUnion₂.mpr ⟨d, hd, hx⟩

/-- p 独立性は全ての有限部分集合で検査できる。 -/
theorem isPIndependentSet_iff_finite (s : Set K) :
    IsPIndependentSet (p := p) s ↔
      ∀ t ⊆ s, t.Finite → IsPIndependentSet (p := p) t := by
  classical
  constructor
  · exact fun hs t hts _ ↦ hs.mono hts
  · intro h
    apply linearIndepOn_of_finite
    intro u hus hu
    let t : Set K := ⋃ d ∈ u, (d.val.support : Set K)
    have ht : t.Finite := hu.biUnion (fun d _ ↦ d.val.support.finite_toSet)
    have hts : t ⊆ s := by
      intro x hx
      obtain ⟨d, hd, hx⟩ := Set.mem_iUnion₂.mp hx
      exact hus hd x hx
    apply LinearIndepOn.mono (h t hts ht)
    intro d hd x hx
    exact Set.mem_iUnion₂.mpr ⟨d, hd, hx⟩

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
  classical
  ext d
  constructor
  · intro hd
    let e : PExponent p s :=
      ⟨d.val.subtypeDomain (· ∈ s), fun i ↦ d.property i.val⟩
    refine ⟨e, Subtype.ext ?_⟩
    apply Finsupp.ext
    intro x
    change (Finsupp.embDomain (Function.Embedding.subtype (· ∈ s)) e.val) x = d.val x
    by_cases hx : x ∈ s
    · exact Finsupp.embDomain_apply_self _ _ (⟨x, hx⟩ : s)
    · rw [Finsupp.embDomain_of_notMem_range _ _ _ (by simpa using hx)]
      exact (Finsupp.notMem_support_iff.mp (fun hmem ↦ hx (hd x hmem))).symm
  · rintro ⟨e, rfl⟩ x hx
    change x ∈ (Finsupp.embDomain (Function.Embedding.subtype (· ∈ s)) e.val).support at hx
    rw [Finsupp.support_embDomain, Finset.mem_map] at hx
    obtain ⟨i, _, hi⟩ := hx
    exact hi ▸ i.property

/-- 共通添字による集合版と、元の集合を添字とする単項式族の独立性との同値。 -/
theorem isPIndependentSet_iff_linearIndependent (s : Set K) :
    IsPIndependentSet (p := p) s ↔
      LinearIndependent (pPowerSubfield K p) (pMonomial (p := p) (Subtype.val : s → K)) := by
  rw [IsPIndependentSet, supportedPExponents_eq_range,
    linearIndepOn_range_iff (PExponent.embDomain_injective _)]
  simp only [Function.comp_def, pMonomial_embDomain]
  rfl

/-- 生成中間体の外の元を集合へ添加しても p 独立性を保つ。 -/
theorem IsPIndependentSet.insert {s : Set K} (hs : IsPIndependentSet (p := p) s)
    (x : K) (hx : x ∉ pMonomialIntermediateField (p := p) (Subtype.val : s → K)) :
    IsPIndependentSet (p := p) (Insert.insert x s) := by
  classical
  have hxS : x ∉ s := by
    intro h
    apply hx
    rw [pMonomialIntermediateField_eq_adjoin]
    exact IntermediateField.subset_adjoin _ _ ⟨⟨x, h⟩, rfl⟩
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
  have hins := hs.prop.insert x hx
  have hxS := hs.mem_of_prop_insert hins
  apply hx
  change x ∈ pMonomialIntermediateField (p := p) (Subtype.val : s → K)
  rw [pMonomialIntermediateField_eq_adjoin]
  exact IntermediateField.subset_adjoin _ _ ⟨⟨x, hxS⟩, rfl⟩

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

end SerrePositivity
