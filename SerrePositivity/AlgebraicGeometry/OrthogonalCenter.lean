module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.BoundaryIdempotentNumerators
public import SerrePositivity.AlgebraicGeometry.IdealFlattening
public import SerrePositivity.AlgebraicGeometry.GeneratorChartCover

/-!
概要：KST §5、Stacks Lemma 31.35.5 の直交する二元による中心。
方針：境界冪の二つの直交成分を中心とし、生成元チャートを分離する。
規約：基礎環の Noether 性は要求しない。
使われ方：境界外の開閉分割を有限生成 blowup 中心で延長する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry Polynomial

variable {R : Type*} [CommRing R]

/--
概要：境界内の二元の和が境界冪なら、その二元中心の補開集合は境界外と一致する。
方針：中心の境界単項イデアルへの包含と、境界冪の中心への所属を使う。
規約：KST §5、Stacks Lemma 31.35.5、直交性はこの等式には不要。
使われ方：開閉部分を分離する blowup の admissible 条件。
-/
theorem pair_center_complement (f a b : R) (N : ℕ)
    (ha : f ∣ a) (hb : f ∣ b) (hab : a + b = f ^ N) :
    affineCenterComplement (Ideal.span {a, b}) = PrimeSpectrum.basicOpen f := by
  have hle : Ideal.span ({a, b} : Set R) ≤ Ideal.span {f} := by
    apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact Ideal.mem_span_singleton.mpr ha
    · rcases Set.mem_singleton_iff.mp hx with rfl
      exact Ideal.mem_span_singleton.mpr hb
  have hpow : f ^ N ∈ Ideal.span ({a, b} : Set R) := by
    rw [← hab]
    exact Ideal.add_mem _ (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))
  apply le_antisymm
  · intro P hP hf
    apply (mem_affineCenterComplement _ P).mp hP
    exact le_trans hle (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hf))
  · exact basicOpen_le_affineCenterComplement_of_pow_mem _ f N hpow

/--
概要：中心の二つの元の積が零なら、対応する標準 blowup チャートは交わらない。
方針：次数一元の積も零であり、斉次素イデアルがどちらかを含むことを使う。
規約：KST §5、Stacks Lemma 31.35.5、中心の生成性は不要。
使われ方：二元中心の標準被覆が開閉分割となることを示す。
-/
theorem disjoint_affineBlowupChart_of_mul_eq_zero (I : Ideal R) (a b : I)
    (hab : a.val * b.val = 0) :
    Disjoint (affineBlowupChart I a) (affineBlowupChart I b) := by
  have hprod : reesDegreeOne I a * reesDegreeOne I b = 0 := by
    apply Subtype.ext
    change Polynomial.monomial 1 a.val * Polynomial.monomial 1 b.val = 0
    rw [Polynomial.monomial_mul_monomial, hab, Polynomial.monomial_zero_right]
  apply disjoint_iff_inf_le.mpr
  intro x hx
  have hz : reesDegreeOne I a * reesDegreeOne I b ∈ x.asHomogeneousIdeal.toIdeal := by
    rw [hprod]
    exact Ideal.zero_mem _
  rcases x.isPrime.mem_or_mem hz with h | h
  · exact hx.1 h
  · exact hx.2 h

/--
概要：二元中心の二つの標準チャートは blowup 全体を覆う。
方針：Bool を添字とする生成族の被覆定理を適用する。
規約：KST §5、Stacks Lemma 31.35.5、二元が零である空チャートも含む。
使われ方：直交する二元中心から二つの開閉部分を作る。
-/
theorem pair_center_chart_sup_eq_top (a b : R) :
    let I := Ideal.span ({a, b} : Set R)
    let x : I := ⟨a, Ideal.subset_span (by simp)⟩
    let y : I := ⟨b, Ideal.subset_span (by simp)⟩
    affineBlowupChart I x ⊔ affineBlowupChart I y = ⊤ := by
  let I := Ideal.span ({a, b} : Set R)
  let x : I := ⟨a, Ideal.subset_span (by simp)⟩
  let y : I := ⟨b, Ideal.subset_span (by simp)⟩
  let C : Bool → I := fun i => if i then x else y
  have hC : Ideal.span (Set.range (fun i => (C i).val)) = I := by
    congr 1
    ext z
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, hi⟩
      cases i <;> simp_all [C, x, y]
    · rintro (rfl | rfl)
      · exact ⟨true, rfl⟩
      · exact ⟨false, rfl⟩
  simpa [iSup_bool_eq, C] using iSup_affineBlowup_generatorCharts I C hC

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
