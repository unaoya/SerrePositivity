module

public import SerrePositivity.KST.SchemeLemmas.ChartAlgebra

/-!
概要：KST §5、Stacks 080Y の共通細分に使う積中心の局所環論。
方針：積イデアルが正則な積 ab で生成されるとき、b を消去して一方の因子を単項化する。
規約：元の環を整域や被約環と仮定しない。
使われ方：Bl_{IJ} の積生成元チャートから Bl_I・Bl_J への射の構成。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.KST.SchemeLemmas
variable {R : Type u} [CommRing R] (I J : Ideal R)

/--
概要：積イデアルが正則な積 ab で生成されるとき、第一のイデアルは a で生成される。
方針：x b の積イデアルへの所属を使い、正則な b を消去する。
規約：KST §5、Stacks 080Y、a ∈ I と b ∈ J を明記する。
使われ方：積中心の blowup で因子中心が局所的に可逆となることの証明。
-/
theorem ideal_eq_span_of_regular_product {a b : R} (ha : a ∈ I) (hb : b ∈ J)
    (hreg : a * b ∈ nonZeroDivisors R) (hIJ : I * J = Ideal.span {a * b}) :
    I = Ideal.span {a} := by
  apply le_antisymm
  · intro x hx
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp
      (hIJ ▸ Ideal.mul_mem_mul hx hb)
    apply Ideal.mem_span_singleton'.mpr
    refine ⟨s, ?_⟩
    apply sub_eq_zero.mp
    apply (mem_nonZeroDivisors_iff_left.mp (mul_mem_nonZeroDivisors.mp hreg).2) (s * a - x)
    rw [mul_comm b, sub_mul, mul_assoc, hs, sub_self]
  · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ha)

/--
概要：二つの中心の元の積を積中心の元として束ねる。
方針：イデアルの積への所属を使う。
規約：KST §5、Stacks 080Y、中心は I J。
使われ方：共通細分の標準チャートの添字。
-/
def mulCenterElement (a : I) (b : J) : ↥(I * J) :=
  ⟨a.1 * b.1, Ideal.mul_mem_mul a.2 b.2⟩

/--
概要：積中心の ab チャートでは a の像は正則。
方針：ab の像の正則性から各因子の正則性を得る。
規約：KST §5、Stacks 080Y、基礎環では a が零因子でもよい。
使われ方：Bl_{IJ} のチャートから Bl_I への普遍写像。
-/
theorem productChart_left_regular (a : I) (b : J) :
    chartBaseMap (I * J) (mulCenterElement I J a b) a.1 ∈
      nonZeroDivisors (BlowupChartRing (I * J) (mulCenterElement I J a b)) := by
  have h := chartBaseMap_mem_nonZeroDivisors (I * J) (mulCenterElement I J a b)
  change chartBaseMap _ _ (a.1 * b.1) ∈ _ at h
  rw [map_mul] at h
  exact (mul_mem_nonZeroDivisors.mp h).1

/--
概要：積中心の ab チャートでは I の拡大は a の像で生成される。
方針：積中心の局所単項性と正則積の消去を使う。
規約：KST §5、Stacks 080Y、有限生成性を使わない。
使われ方：共通細分の第一の比較射の局所条件。
-/
theorem productChart_left_image (a : I) (b : J) :
    I.map (chartBaseMap (I * J) (mulCenterElement I J a b)) =
      Ideal.span {chartBaseMap (I * J) (mulCenterElement I J a b) a.1} := by
  let φ := chartBaseMap (I * J) (mulCenterElement I J a b)
  apply ideal_eq_span_of_regular_product (I.map φ) (J.map φ)
    (Ideal.mem_map_of_mem φ a.2) (Ideal.mem_map_of_mem φ b.2)
  · rw [← map_mul]
    exact chartBaseMap_mem_nonZeroDivisors (I * J) (mulCenterElement I J a b)
  · rw [← Ideal.map_mul, ← map_mul]
    exact chart_map_ideal_eq_span (I * J) (mulCenterElement I J a b)

end SerrePositivity.KST.SchemeLemmas
