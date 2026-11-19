module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.OrthogonalCenter
public import Mathlib.RingTheory.Finiteness.Basic

/-!
概要：KST §5、Stacks Lemma 31.35.5 の境界外の冪等元を分離する実際の中心。
方針：直交する分子を中心に選び、二つの生成元チャートの境界外で冪等元を 1 と 0 にする。
規約：通常の Rees Proj のチャートとその実際の局所化準同型を使う。
使われ方：境界外の一般階数の開閉部分を blowup 上の開閉部分へ延長する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry

variable {R : Type*} [CommRing R]

/--
概要：分子がチャート内で境界冪に等しければ、境界外で対応する局所化元の像は 1。
方針：分子の等式を局所化写像へ送り、可逆な境界冪を打ち消す。
規約：KST §5、Stacks Lemma 31.35.5、局所化元の冪等性は不要。
使われ方：開閉部分を分離する一方のチャートの判定。
-/
theorem awayMap_eq_one_of_numerator (f : R) (e : Localization.Away f) (a : R) (N : ℕ)
    (ha : algebraMap R (Localization.Away f) a =
      e * algebraMap R (Localization.Away f) f ^ N)
    {S : Type*} [CommRing S] (φ : R →+* S) (hφ : φ a = φ f ^ N) :
    Localization.awayMap φ f e = 1 := by
  let ψ := Localization.awayMap φ f
  have hcomm (r : R) : ψ (algebraMap R (Localization.Away f) r) =
      algebraMap S (Localization.Away (φ f)) (φ r) := by
    simp [ψ, IsLocalization.Away.map]
  apply ((IsLocalization.Away.algebraMap_isUnit (φ f)).pow N).mul_right_cancel
  have h := congrArg ψ ha
  rw [map_mul, map_pow, hcomm, hcomm, hφ, map_pow] at h
  simpa only [one_mul] using h.symm

/--
概要：分子がチャート内で零なら、境界外で対応する局所化元の像は零。
方針：分子の等式を局所化写像へ送り、可逆な境界冪を打ち消す。
規約：KST §5、Stacks Lemma 31.35.5、局所化元の冪等性は不要。
使われ方：開閉部分を分離するもう一方のチャートの判定。
-/
theorem awayMap_eq_zero_of_numerator (f : R) (e : Localization.Away f) (a : R) (N : ℕ)
    (ha : algebraMap R (Localization.Away f) a =
      e * algebraMap R (Localization.Away f) f ^ N)
    {S : Type*} [CommRing S] (φ : R →+* S) (hφ : φ a = 0) :
    Localization.awayMap φ f e = 0 := by
  let ψ := Localization.awayMap φ f
  have hcomm (r : R) : ψ (algebraMap R (Localization.Away f) r) =
      algebraMap S (Localization.Away (φ f)) (φ r) := by
    simp [ψ, IsLocalization.Away.map]
  apply ((IsLocalization.Away.algebraMap_isUnit (φ f)).pow N).mul_right_cancel
  have h := congrArg ψ ha
  rw [map_mul, map_pow, hcomm, hcomm, hφ, map_zero] at h
  simpa only [zero_mul] using h.symm

/--
概要：境界外の冪等元を二つの互いに交わらない生成元チャートで分離する有限生成中心が存在する。
方針：実際の直交分子を選び、チャートの非零因子性と局所化写像の等式を接続する。
規約：KST §5、Stacks Lemma 31.35.5、中心補開集合は正確に D(f)。
使われ方：境界外の開閉分割を延長して一般階数一定の特殊形へ還元する。
-/
theorem exists_fg_center_separating_boundary_idempotent (f : R) (hf : IsRegular f)
    (e : Localization.Away f) (he : IsIdempotentElem e) :
    ∃ (I : Ideal R) (a b : I),
      I.FG ∧ affineCenterComplement I = PrimeSpectrum.basicOpen f ∧
      Disjoint (affineBlowupChart I a) (affineBlowupChart I b) ∧
      affineBlowupChart I a ⊔ affineBlowupChart I b = ⊤ ∧
      Localization.awayMap (chartBaseMap I a) f e = 1 ∧
      Localization.awayMap (chartBaseMap I b) f e = 0 := by
  obtain ⟨N, a, b, _, hfa, hfb, hsum, hab, hnum⟩ :=
    exists_orthogonal_boundary_numerators f hf e he
  let I := Ideal.span ({a, b} : Set R)
  let x : I := ⟨a, Ideal.subset_span (by simp)⟩
  let y : I := ⟨b, Ideal.subset_span (by simp)⟩
  refine ⟨I, x, y, Submodule.fg_span (Set.toFinite _),
    pair_center_complement f a b N hfa hfb hsum,
    disjoint_affineBlowupChart_of_mul_eq_zero I x y hab,
    pair_center_chart_sup_eq_top a b, ?_, ?_⟩
  · apply awayMap_eq_one_of_numerator f e a N hnum
    have hb : chartBaseMap I x b = 0 := chartBaseMap_eq_zero_of_mul_eq_zero I x b hab
    have hs := congrArg (chartBaseMap I x) hsum
    simpa only [map_add, hb, add_zero, map_pow] using hs
  · apply awayMap_eq_zero_of_numerator f e a N hnum
    exact chartBaseMap_eq_zero_of_mul_eq_zero I y a (by simpa [mul_comm] using hab)

/--
概要：境界外の任意の開閉部分を二つの互いに交わらない実チャートで分離する有限生成中心が存在する。
方針：開閉部分を冪等元の基本開集合で表し、冪等元を分離する中心の定理を使う。
規約：KST §5、Stacks Lemma 31.35.5、二つのチャートは通常の blowup 全体を覆う。
使われ方：境界外の階数の開閉部分を分離し、一定階数の場合へ還元する。
-/
theorem exists_fg_center_separating_boundary_clopen (f : R) (hf : IsRegular f)
    (s : Set (PrimeSpectrum (Localization.Away f))) (hs : IsClopen s) :
    ∃ (I : Ideal R) (a b : I),
      I.FG ∧ affineCenterComplement I = PrimeSpectrum.basicOpen f ∧
      Disjoint (affineBlowupChart I a) (affineBlowupChart I b) ∧
      affineBlowupChart I a ⊔ affineBlowupChart I b = ⊤ ∧
      (PrimeSpectrum.comap (Localization.awayMap (chartBaseMap I a) f)) ⁻¹' s = Set.univ ∧
      (PrimeSpectrum.comap (Localization.awayMap (chartBaseMap I b) f)) ⁻¹' s = ∅ := by
  obtain ⟨e, he, hse⟩ := PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen hs
  obtain ⟨I, a, b, hfg, hI, hd, hc, h1, h0⟩ :=
    exists_fg_center_separating_boundary_idempotent f hf e he
  refine ⟨I, a, b, hfg, hI, hd, hc, ?_, ?_⟩
  · rw [hse]
    ext P
    change (Localization.awayMap (chartBaseMap I a) f e ∉ P.asIdeal) ↔ True
    rw [h1]
    exact iff_true_intro P.isPrime.one_notMem
  · rw [hse]
    ext P
    change (Localization.awayMap (chartBaseMap I b) f e ∉ P.asIdeal) ↔ False
    simp [h0]

end SerrePositivity.AlgebraicGeometry


/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
