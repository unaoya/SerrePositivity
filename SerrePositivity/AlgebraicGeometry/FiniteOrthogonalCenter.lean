module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.FiniteBoundaryNumerators
public import SerrePositivity.AlgebraicGeometry.BoundaryClopenSeparation

/-!
概要：KST §5、Stacks Lemma 31.35.5 の境界外の有限分割を分離する実際の blowup 中心。
方針：直交分子の有限族を中心とし、実際の生成元チャートで冪等元の像を計算する。
規約：通常の Rees Proj と標準チャートを使い、合成 blowup の存在を仮定しない。
使われ方：一般階数の有限個の開閉部分を一段の blowup で分離する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry

variable {R ι : Type*} [CommRing R] [Fintype ι]

/--
概要：境界内の有限個の元の総和が境界冪なら、その生成中心の補開集合は境界外。
方針：中心の境界単項イデアルへの包含と総和の中心への所属を使う。
規約：KST §5、Stacks Lemma 31.35.5、直交性はこの等式には不要。
使われ方：有限分割を分離する中心の admissible 条件。
-/
theorem finite_center_complement (f : R) (a : ι → R) (N : ℕ)
    (ha : ∀ i, f ∣ a i) (hsum : (∑ i, a i) = f ^ N) :
    affineCenterComplement (Ideal.span (Set.range a)) = PrimeSpectrum.basicOpen f := by
  let I := Ideal.span (Set.range a)
  have hle : I ≤ Ideal.span {f} := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Ideal.mem_span_singleton.mpr (ha i)
  have hpow : f ^ N ∈ I := by
    rw [← hsum]
    exact I.sum_mem (fun i _ => Ideal.subset_span ⟨i, rfl⟩)
  apply le_antisymm
  · intro P hP hf
    apply (mem_affineCenterComplement I P).mp hP
    exact le_trans hle (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hf))
  · exact basicOpen_le_affineCenterComplement_of_pow_mem I f N hpow

/--
概要：境界外の完全直交冪等元の有限族を、互いに交わらない有限チャートで分離する中心が存在する。
方針：共通分母の直交分子を中心とし、チャート中心元の正則性で他の分子を消す。
規約：KST §5、Stacks Lemma 31.35.5、中心は有限生成で補開集合は正確に D(f)。
使われ方：有限個の一般階数の部分を一段で分離する。
-/
theorem exists_fg_center_separating_boundary_idempotents (f : R) (hf : IsRegular f)
    (e : ι → Localization.Away f) (he : CompleteOrthogonalIdempotents e) :
    ∃ (I : Ideal R) (a : ι → I),
      I.FG ∧ affineCenterComplement I = PrimeSpectrum.basicOpen f ∧
      (⨆ i, affineBlowupChart I (a i)) = ⊤ ∧
      Pairwise (fun i j => Disjoint (affineBlowupChart I (a i)) (affineBlowupChart I (a j))) ∧
      (∀ i, Localization.awayMap (chartBaseMap I (a i)) f (e i) = 1) ∧
      ∀ i j, i ≠ j → Localization.awayMap (chartBaseMap I (a i)) f (e j) = 0 := by
  classical
  obtain ⟨N, b, _, hfb, hsum, hb, hnum⟩ :=
    exists_finite_orthogonal_boundary_numerators f hf e he
  let I := Ideal.span (Set.range b)
  let a : ι → I := fun i => ⟨b i, Ideal.subset_span ⟨i, rfl⟩⟩
  have hzero (i j : ι) (hij : i ≠ j) : chartBaseMap I (a i) (b j) = 0 :=
    chartBaseMap_eq_zero_of_mul_eq_zero I (a i) (b j) (hb hij)
  refine ⟨I, a, Submodule.fg_span (Set.finite_range b),
    finite_center_complement f b N hfb hsum,
    iSup_affineBlowup_generatorCharts I a rfl, ?_, ?_, ?_⟩
  · intro i j hij
    exact disjoint_affineBlowupChart_of_mul_eq_zero I (a i) (a j) (hb hij)
  · intro i
    apply awayMap_eq_one_of_numerator f (e i) (b i) N (hnum i)
    have hs := congrArg (chartBaseMap I (a i)) hsum
    rw [map_sum, map_pow] at hs
    rwa [Finset.sum_eq_single i (fun j _ hji => hzero i j hji.symm) (by simp)] at hs
  · intro i j hij
    exact awayMap_eq_zero_of_numerator f (e j) (b j) N (hnum j)
      (chartBaseMap I (a i)) (hzero i j hij)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
