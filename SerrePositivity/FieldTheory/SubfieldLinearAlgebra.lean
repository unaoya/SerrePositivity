module

public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.RingTheory.AlgebraTower
public import Mathlib.RingTheory.Finiteness.Basic

/-! # 部分体上の線形代数

概要：体の部分体を係数とする線形包・独立性・有限性の補題。
- 係数ごとの判定：`E ≤ S` で `v` が `S` 上独立なら、`x ∈ span E v` ⟺ `x` の `S` 上の座標がすべて `E` に入る。
- 有向な族の交わり：下向き有向な部分体族の一つの上で `v` が独立なら、`x` がすべての `span Eᵢ v` に入る ⟺
  `x ∈ span (⋂ Eᵢ) v`。
- 係数制限、部分体の合成の線形包による計算、部分体上の有限性。
方針：係数は `Finsupp` で扱い、添字の有限性は要求しない。
規約：体の標数や p-rank は要求しない。Mathlib の `Module.Basis.mem_span_iff_repr_mem`（基底の場合）の独立族版にあたる。
使われ方：p 乗部分体の族の交わりの計算（`PrimeRootPowerSubfield`・`PowerSubfieldFamilyIntersection` など）。
-/

@[expose] public noncomputable section
namespace SerrePositivity

section Span

variable {K τ ι : Type*} [Field K]

/-- 係数がすべて `E` に入る有限和は、`E` 上の線形包に入る。 -/
theorem sum_mem_subfield_span (E : Subfield K) (v : τ → K) (c : τ →₀ K) (hc : ∀ t, c t ∈ E) :
    (c.sum fun t a ↦ a * v t) ∈ Submodule.span E (Set.range v) :=
  Submodule.sum_mem _ fun t _ ↦ by
    have h := (Submodule.span E (Set.range v)).smul_mem (⟨c t, hc t⟩ : E)
      (Submodule.subset_span (R := E) ⟨t, rfl⟩)
    simpa [Algebra.smul_def, Subfield.algebraMap_ofSubfield] using h

/-- 係数ごとの判定：`E ≤ S` で `v` が `S` 上独立なら、`S` 上の線形包の元 `x` について、
`x ∈ span E v` ⟺ `x` の `S` 上の座標がすべて `E` に入る。 -/
theorem mem_subfield_span_iff_repr_mem (E S : Subfield K) (hES : E ≤ S) (v : τ → K)
    (hv : LinearIndependent S v) (x : K) (hx : x ∈ Submodule.span S (Set.range v)) :
    x ∈ Submodule.span E (Set.range v) ↔ ∀ t, (hv.repr ⟨x, hx⟩ t : K) ∈ E := by
  constructor
  · intro h t
    obtain ⟨d, hd⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).mp h
    let dS : τ →₀ S := d.mapRange (Subfield.inclusion hES) (map_zero _)
    have : hv.repr ⟨x, hx⟩ = dS := by
      apply hv.repr_eq
      simp [dS, ← hd, Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index,
        Algebra.smul_def, Subfield.algebraMap_ofSubfield]
      rfl
    rw [this]
    exact (d t).property
  · intro h
    have hsum : Finsupp.linearCombination S v (hv.repr ⟨x, hx⟩) = x :=
      hv.linearCombination_repr ⟨x, hx⟩
    have hx' : x = ((hv.repr ⟨x, hx⟩).mapRange ((↑) : S → K) rfl).sum fun t a ↦ a * v t := by
      conv_lhs => rw [← hsum]
      rw [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (by simp)]
      simp [Algebra.smul_def, Subfield.algebraMap_ofSubfield]
    rw [hx']
    exact sum_mem_subfield_span E v _ fun t ↦ by simpa using h t

/-- 下向き有向な部分体族の一つの上で `v` が独立なら、`x` がすべての `span Eᵢ v` に入ることと、
交わり上の線形包に入ることは同値。添字 `τ` の有限性は不要。 -/
theorem mem_all_subfield_spans_iff (E : ι → Subfield K)
    (hdir : Directed (· ≥ ·) E)
    (v : τ → K) (hind : ∃ j, LinearIndependent (E j) v) (x : K) :
    (∀ i, x ∈ Submodule.span (E i) (Set.range v)) ↔
      x ∈ Submodule.span ↥(⨅ i, E i) (Set.range v) := by
  constructor
  · intro hx
    obtain ⟨j, hj⟩ := hind
    have hcoeff (t : τ) : (hj.repr ⟨x, hx j⟩ t : K) ∈ ⨅ i, E i := by
      apply Subfield.mem_iInf.mpr
      intro i
      obtain ⟨k, hki, hkj⟩ := hdir i j
      exact hki ((mem_subfield_span_iff_repr_mem (E k) (E j) hkj v hj x (hx j)).mp (hx k) t)
    rw [(mem_subfield_span_iff_repr_mem (⨅ i, E i) (E j) (iInf_le E j) v hj x (hx j))]
    exact hcoeff
  · intro hx i
    obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).mp hx
    have hx' : x = (c.mapRange ((↑) : ↥(⨅ i, E i) → K) rfl).sum fun t a ↦ a * v t := by
      rw [← hc, Finsupp.sum_mapRange_index (by simp)]
      simp [Algebra.smul_def, Subfield.algebraMap_ofSubfield]
    rw [hx']
    exact sum_mem_subfield_span (E i) v _ fun t ↦ by
      simpa using (Subfield.mem_iInf.mp (c t).property) i

end Span

section Extension

variable {K L τ : Type*} [Field K] [Field L] [Algebra K L]

/-- 体上の独立性を、同じ係数作用を持つ埋め込みの像上へ移す。 -/
theorem linearIndependent_fieldRange (v : τ → L) (hv : LinearIndependent K v) :
    LinearIndependent (algebraMap K L).fieldRange v := by
  let e := (algebraMap K L).rangeRestrictFieldEquiv
  have h := hv.map_of_injective_injectiveₛ e.symm (AddMonoidHom.id L) e.symm.injective
    Function.injective_id (fun r m ↦ ?_)
  · exact h
  · have hr := congrArg (fun c : (algebraMap K L).fieldRange ↦ (c : L))
      (e.apply_symm_apply r)
    change algebraMap K L (e.symm r) = (r : L) at hr
    simp only [Algebra.smul_def, AddMonoidHom.id_apply, Subfield.algebraMap_ofSubfield]
    change algebraMap K L (e.symm r) * m = (r : L) * m
    rw [hr]

/-- 部分体の包含に沿って独立性を係数制限する。 -/
theorem linearIndependent_subfield_of_le {E S : Subfield L} (hES : E ≤ S)
    (v : τ → L) (hv : LinearIndependent S v) : LinearIndependent E v := by
  exact hv.map_of_injective_injectiveₛ (Subfield.inclusion hES) (AddMonoidHom.id L)
    (RingHom.injective (Subfield.inclusion hES)) Function.injective_id (fun _ _ ↦ rfl)

/-- 部分体の合成を、共通の小さい底体での生成族の線形包として計算する。
有限性は合成が部分代数と中間体のどちらでも同じになるために使う。 -/
theorem mem_subfield_sup_iff_mem_span
    (F E S : Subfield L) [Module.Finite E L] (hFE : F ≤ E)
    (v : τ → L) (hspan : (S : Set L) = (Submodule.span F (Set.range v) : Set L)) (z : L) :
    z ∈ E ⊔ S ↔ z ∈ Submodule.span E (Set.range v) := by
  let : Algebra F E := (Subfield.inclusion hFE).toAlgebra
  let : IsScalarTower F E L := IsScalarTower.of_algebraMap_eq' (R := F) (S := E) (A := L) rfl
  have heq : (IntermediateField.adjoin E (S : Set L)).toSubfield = E ⊔ S := by
    rw [IntermediateField.adjoin_toSubfield]
    have hr : Set.range (algebraMap E L) = (E : Set L) := by
      ext y
      constructor
      · rintro ⟨c, rfl⟩; exact c.property
      · intro hy; exact ⟨⟨y, hy⟩, rfl⟩
    rw [hr, Subfield.closure_union, Subfield.closure_eq, Subfield.closure_eq]
  rw [← heq]
  change z ∈ (IntermediateField.adjoin E (S : Set L)).toSubalgebra.toSubmodule ↔ _
  rw [IntermediateField.adjoin_toSubalgebra]
  change z ∈ (Algebra.adjoin E (S.toSubmonoid : Set L)).toSubmodule ↔ _
  rw [S.toSubmonoid.adjoin_eq_span_of_eq_span F E hspan]

end Extension

section Finite

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- 共有限な部分体の像を含む、有限拡大内の部分体も共有限。 -/
theorem finite_subfield_of_map_le
    (E : Subfield K) (G : Subfield L) (hEG : E.map (algebraMap K L) ≤ G)
    [Module.Finite E K] [Module.Finite K L] : Module.Finite G L := by
  let f : E →+* L := (algebraMap K L).comp E.subtype
  let : Algebra E L := f.toAlgebra
  let : Module E L := @Algebra.toModule _ _ _ _ (inferInstance : Algebra E L)
  let : SMul E L := (inferInstance : Algebra E L).toSMul
  let : IsScalarTower E K L := IsScalarTower.of_algebraMap_eq' (R := E) (S := K) (A := L) rfl
  let : Module.Finite E L := Module.Finite.trans (R := E) K L
  let g : E →+* G := f.codRestrict G (fun c ↦ hEG (Subfield.mem_map.mpr ⟨c, c.property, rfl⟩))
  let : Algebra E G := g.toAlgebra
  let : IsScalarTower E G L := IsScalarTower.of_algebraMap_eq' (R := E) (S := G) (A := L) rfl
  exact Module.Finite.of_restrictScalars_finite E G L

end Finite

end SerrePositivity
