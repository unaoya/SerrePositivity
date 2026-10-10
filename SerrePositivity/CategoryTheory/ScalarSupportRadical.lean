module

public import SerrePositivity.CategoryTheory.ScalarSupport
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Finiteness.Ideal

/-! # スカラー支持は生成イデアルの根基だけに依存する

任意の線形圏で、恒等射の消去条件を自己準同型加群の消去イデアルで表す。
有限なパラメータ系の変更に使い、Noether 性や三角圏の構造は要求しない。
-/

@[expose] public section

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits

variable {R : Type*} [CommRing R] {C : Type*} [Category* C] [Preadditive C] [Linear R C]
  {ι κ : Type*} (z : ι → R)

/-- 恒等射を消すスカラーは、すべての自己準同型を消す。 -/
lemma smul_id_eq_zero_iff_mem_annihilator (X : C) (a : R) :
    a • 𝟙 X = 0 ↔ a ∈ Module.annihilator R (X ⟶ X) := by
  rw [Module.mem_annihilator]
  constructor
  · intro ha f
    simpa only [Linear.smul_comp, Category.id_comp, zero_comp] using ha =≫ f
  · intro ha
    exact ha (𝟙 X)

/-- 有限パラメータ系の支持は、その生成イデアルが自己準同型の消去イデアルの根基に入ること。 -/
lemma scalarSupported_iff_le_radical_annihilator [Finite ι] (X : C) :
    scalarSupported z X ↔
      Ideal.span (Set.range z) ≤ (Module.annihilator R (X ⟶ X)).radical := by
  classical
  let := Fintype.ofFinite ι
  constructor
  · rintro ⟨v, _, hv⟩
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact ⟨v, (smul_id_eq_zero_iff_mem_annihilator X _).mp (hv j)⟩
  · intro h
    have hj (j : ι) : ∃ v : ℕ, z j ^ v • 𝟙 X = 0 := by
      obtain ⟨v, hv⟩ := h (Ideal.subset_span ⟨j, rfl⟩)
      exact ⟨v, (smul_id_eq_zero_iff_mem_annihilator X _).mpr hv⟩
    choose v hv using hj
    refine ⟨Finset.univ.sup v + 1, by omega, fun j ↦ ?_⟩
    exact pow_smul_id_eq_zero_of_le (hv j)
      ((Finset.le_sup (Finset.mem_univ j)).trans (Nat.le_succ _))

/-- 生成イデアルの根基の包含に沿って、支持条件を移す。 -/
lemma scalarSupported_of_span_le_radical [Finite ι] [Finite κ] (w : κ → R)
    (h : Ideal.span (Set.range w) ≤ (Ideal.span (Set.range z)).radical)
    {X : C} (hX : scalarSupported z X) : scalarSupported w X := by
  rw [scalarSupported_iff_le_radical_annihilator] at hX ⊢
  exact h.trans (by simpa only [Ideal.radical_idem] using Ideal.radical_mono hX)

/-- 根基が同じ有限パラメータ系は、全く同じ支持部分圏を定める。 -/
lemma scalarSupported_eq_of_radical_eq [Finite ι] [Finite κ] (w : κ → R)
    (h : (Ideal.span (Set.range z)).radical = (Ideal.span (Set.range w)).radical) :
    scalarSupported (C := C) z = scalarSupported w := by
  funext X
  apply propext
  constructor
  · exact scalarSupported_of_span_le_radical z w (Ideal.le_radical.trans_eq h.symm)
  · exact scalarSupported_of_span_le_radical w z (Ideal.le_radical.trans_eq h)

end SerrePositivity
