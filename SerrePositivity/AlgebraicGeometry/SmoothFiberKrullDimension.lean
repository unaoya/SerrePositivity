module

public import SerrePositivity.AlgebraicGeometry.AffineSectionComponentLocus
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.Unramified.LocalStructure

/-!
概要：一定の相対次元を持つ滑らかなアフィン射のファイバーの Krull 次元を抑える。
方針：体上の標準滑らかなチャートを多項式環上の étale 代数にし、素イデアルの鎖を比較する。
規約：結論は Krull 次元の上限として述べ、空ファイバーも許す。
使われ方：相対 Noether 正規化先で、余核による帰納の次元上限を得る。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory
open scoped TensorProduct

private theorem ringKrullDim_le_of_quasiFinite
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Algebra.QuasiFinite A B] :
    ringKrullDim B ≤ ringKrullDim A := by
  apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A B))
  intro p q hpq
  refine lt_of_le_of_ne (Ideal.comap_mono hpq.le) fun he => hpq.ne ?_
  exact PrimeSpectrum.ext (Algebra.QuasiFinite.eq_of_le_of_under_eq (R := A) p.asIdeal q.asIdeal
    hpq.le (congrArg PrimeSpectrum.asIdeal he))

/--
概要：体上の相対次元 `n` の滑らかなアフィン射の始域の Krull 次元は `n` 以下。
方針：各素点を含む標準滑らかな主開を取り、étale な多項式模型でその次元を評価する。
規約：相対次元は Mathlib のスキーム射の条件を使う。
使われ方：次元を制御した相対正規化先を余核の帰納に渡す。
-/
theorem ringKrullDim_le_of_smoothOfRelativeDimension_spec
    {K B : Type u} [Field K] [CommRing B] [Algebra K B] (n : ℕ)
    [SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap K B)))] :
    ringKrullDim B ≤ n := by
  have hl : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap K B) :=
    (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)
      (φ := CommRingCat.ofHom (algebraMap K B))).mp inferInstance
  obtain ⟨s, hs, hstd⟩ := hl
  apply (ringKrullDim_le_iff_height_le _).mpr
  intro p hp
  have hx : ∃ b ∈ s, b ∉ p := by
    by_contra h
    push Not at h
    have htop := hs ▸ Ideal.span_le.mpr h
    exact hp.ne_top (top_le_iff.mp htop)
  obtain ⟨b, hb, hbp⟩ := hx
  let L := Localization.Away b
  let P := MvPolynomial (Fin n) K
  obtain ⟨g, _, hg⟩ := (hstd b hb).exists_etale_mvPolynomial
  let : Algebra P L := g.toAlgebra
  let : Algebra.Etale P L := hg
  have hdim : ringKrullDim L ≤ (n : WithBot ℕ∞) := by
    calc
      ringKrullDim L ≤ ringKrullDim P := ringKrullDim_le_of_quasiFinite P L
      _ = n := by
        simp [P, MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
          ringKrullDim_eq_zero_of_field]
  have hdisj : Disjoint (Submonoid.powers b : Set B) (p : Set B) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime b).mpr hbp
  let : (p.map (algebraMap B L)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (.powers b) L p hp hdisj
  rw [← IsLocalization.height_map_of_disjoint (S := L) (.powers b) p hdisj]
  exact (p.map (algebraMap B L)).height_le_ringKrullDim_of_isPrime.trans hdim

/--
概要：相対次元 `n` の滑らかなアフィン射の任意の剰余体ファイバーの Krull 次元は `n` 以下。
方針：滑らかさと相対次元を剰余体へ底変換し、体上の評価を適用する。
規約：ファイバー環の剰余体をテンソル積の右因子に置く。
使われ方：Stacks 0815 で、正規化先の各ファイバー上で余核の台の次元を下げる。
-/
theorem ringKrullDim_fiber_le_of_smoothOfRelativeDimension_spec
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] (n : ℕ)
    [SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap R B)))]
    (p : PrimeSpectrum R) : ringKrullDim (B ⊗[R] p.asIdeal.ResidueField) ≤ n := by
  let K := p.asIdeal.ResidueField
  let f := Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[R] B)))
  let : SmoothOfRelativeDimension n f :=
    MorphismProperty.of_isPullback (isPullback_specTensor R B K) inferInstance
  rw [ringKrullDim_eq_of_ringEquiv (Algebra.TensorProduct.comm R B K).toRingEquiv]
  exact ringKrullDim_le_of_smoothOfRelativeDimension_spec (K := K) n

end SerrePositivity.AlgebraicGeometry
