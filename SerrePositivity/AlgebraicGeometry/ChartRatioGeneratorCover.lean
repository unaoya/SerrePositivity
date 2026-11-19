module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.ChartAlgebra

/-!
概要：KST §5、Stacks 0815 の中心の生成族によるチャート内の基本開被覆。
方針：中心元 a の像を打ち消し、生成元の比が単位イデアルを生成することを示す。
規約：中心の有限生成性は不要。
使われ方：生成元チャート上の平坦性を任意のチャートへ移す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

variable {R ι : Type*} [CommRing R] (I : Ideal R) (a : I) (C : ι → I)

/--
概要：中心の生成元を a で割ったチャート内の比は単位イデアルを生成する。
方針：元の中心の像を a と比のイデアルの積に入れ、a の正則性で一を得る。
規約：KST §5、Stacks 0815、生成族は任意の添字集合でよい。
使われ方：チャートの重なりでの平坦性の局所判定。
-/
theorem span_chartRatio_generators_eq_top
    (hC : Ideal.span (Set.range (fun i => (C i).val)) = I) :
    Ideal.span (Set.range (fun i => chartRatio I a (C i))) = ⊤ := by
  let J := Ideal.span (Set.range (fun i => chartRatio I a (C i)))
  have hle : I.map (chartBaseMap I a) ≤ Ideal.span {chartBaseMap I a a.val} * J := by
    apply Ideal.map_le_iff_le_comap.mpr
    apply le_trans hC.ge
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change chartBaseMap I a (C i).val ∈ Ideal.span {chartBaseMap I a a.val} * J
    rw [← chartBaseMap_mul_ratio I a (C i)]
    exact Ideal.mul_mem_mul (Ideal.subset_span (Set.mem_singleton _))
      (Ideal.subset_span ⟨i, rfl⟩)
  have ha : chartBaseMap I a a.val ∈ Ideal.span {chartBaseMap I a a.val} * J :=
    hle (Ideal.mem_map_of_mem _ a.property)
  obtain ⟨s, hs, heq⟩ := Ideal.mem_span_singleton_mul.mp ha
  have hs1 : s = 1 := by
    apply sub_eq_zero.mp
    apply (mem_nonZeroDivisors_iff_left.mp (chartBaseMap_mem_nonZeroDivisors I a)) (s - 1)
    rw [mul_sub, heq, mul_one, sub_self]
  exact Ideal.eq_top_of_isUnit_mem J (hs1 ▸ hs) isUnit_one

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
