module

public import SerrePositivity.AlgebraicGeometry.FiniteClopenIdempotents
public import SerrePositivity.AlgebraicGeometry.FiniteOrthogonalCenter

/-!
概要：KST §5、Stacks Lemma 31.35.5 の境界外の有限開閉分割を分離する中心。
方針：有限開閉分割を完全直交冪等元で表し、共通分母の分子中心を使う。
規約：実際の有限生成中心と、互いに交わらず全体を覆う標準チャートを返す。
使われ方：境界外の有限個の階数部分をチャートで分離する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry

variable {R ι : Type*} [CommRing R] [Finite ι]

/--
概要：境界外の有限開閉分割には各部分を分離する有限標準チャート被覆を持つ有限生成中心が存在する。
方針：完全直交冪等元の分子中心により、境界外の各部分の逆像を全体または空にする。
規約：KST §5、Stacks Lemma 31.35.5、中心補開集合は正確に D(f)。
使われ方：一般階数の開閉部分ごとに一定階数の中心の定理を適用する準備。
-/
theorem exists_fg_center_separating_boundary_finite_clopen_partition
    (f : R) (hf : IsRegular f)
    (s : ι → Set (PrimeSpectrum (Localization.Away f))) (hs : ∀ i, IsClopen (s i))
    (hd : Pairwise (fun i j => Disjoint (s i) (s j))) (hc : (⋃ i, s i) = Set.univ) :
    ∃ (I : Ideal R) (a : ι → I),
      I.FG ∧ affineCenterComplement I = PrimeSpectrum.basicOpen f ∧
      (⨆ i, affineBlowupChart I (a i)) = ⊤ ∧
      Pairwise (fun i j => Disjoint (affineBlowupChart I (a i)) (affineBlowupChart I (a j))) ∧
      (∀ i, (PrimeSpectrum.comap (Localization.awayMap (chartBaseMap I (a i)) f)) ⁻¹'
        s i = Set.univ) ∧
      ∀ i j, i ≠ j →
        (PrimeSpectrum.comap (Localization.awayMap (chartBaseMap I (a i)) f)) ⁻¹' s j = ∅ := by
  let : Fintype ι := Fintype.ofFinite ι
  obtain ⟨e, he, hse⟩ :=
    exists_completeOrthogonalIdempotents_of_finite_clopen_partition s hs hd hc
  obtain ⟨I, a, hfg, hI, hcover, hdisj, h1, h0⟩ :=
    exists_fg_center_separating_boundary_idempotents f hf e he
  refine ⟨I, a, hfg, hI, hcover, hdisj, ?_, ?_⟩
  · intro i
    rw [hse i]
    ext P
    change (Localization.awayMap (chartBaseMap I (a i)) f (e i) ∉ P.asIdeal) ↔ True
    rw [h1 i]
    exact iff_true_intro P.isPrime.one_notMem
  · intro i j hij
    rw [hse j]
    ext P
    change (Localization.awayMap (chartBaseMap I (a i)) f (e j) ∉ P.asIdeal) ↔ False
    simp [h0 i j hij]

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
