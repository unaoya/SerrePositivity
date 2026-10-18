module

public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.AlgebraicGeometry.Scheme

/-!
# 中心元を逆にした後の閉台の消滅

## 概要
閉台を定めるイデアルの根基に入る元を逆にすると、その台の逆像は空になる。

## 方針
素イデアルは単元を含まないことを、根基の冪による判定へ適用する。

## 規約
Noether 性・有限生成性は不要。係数代数に可換性を要求する主張ではない。

## 使われ方
論文 (3.5)–(3.6) の p ∈ J による台の消滅。TT の局所化列を入れる前の幾何入力。
-/

@[expose] public section

universe u v

open AlgebraicGeometry CategoryTheory

namespace SerrePositivity.KST.Descent

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-- 概要：イデアルの元が単元に写るなら閉台の逆像は空（論文 (3.6)）。
方針：素イデアルが単元を含まないことを使う。
規約：局所化射以外の任意の環準同型にも適用可能。
使われ方：中心局所化後の支持圏の消滅。 -/
theorem support_preimage_empty_of_isUnit (φ : A →+* B) (J : Ideal A) (p : A)
    (hp : p ∈ J) (hunit : IsUnit (φ p)) :
    PrimeSpectrum.comap φ ⁻¹' PrimeSpectrum.zeroLocus (J : Set A) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro q hq
  exact q.asIdeal.notMem_of_isUnit hunit (hq hp)

/-- 概要：根基に入る元が単元に写るだけで閉台の逆像は空（論文 (3.6)）。
方針：イデアルに入る冪を選び、単元の冪に前の判定を適用する。
規約：p ∈ J より弱い根基条件で述べる。
使われ方：パラメータ系と剰余標数による支持条件の比較。 -/
theorem support_preimage_empty_of_radical_isUnit (φ : A →+* B) (J : Ideal A) (p : A)
    (hp : p ∈ J.radical) (hunit : IsUnit (φ p)) :
    PrimeSpectrum.comap φ ⁻¹' PrimeSpectrum.zeroLocus (J : Set A) = ∅ := by
  obtain ⟨n, hn⟩ := hp
  exact support_preimage_empty_of_isUnit φ J (p ^ n) hn
    ((φ.map_pow p n).symm ▸ hunit.pow n)

variable [Algebra A B]

/-- 概要：指定された中心局所化で閉台が消える（論文 (3.5)–(3.6)）。
方針：Away 局所化で指定中心元が単元になることを根基の判定へ渡す。
規約：特定の局所化環の模型に依存しない。
使われ方：Y = S, X における (3.6) の TT 局所化への接続。 -/
theorem support_preimage_empty_after_inversion (J : Ideal A) (p : A)
    [IsLocalization.Away p B] (hp : p ∈ J.radical) :
    PrimeSpectrum.comap (algebraMap A B) ⁻¹' PrimeSpectrum.zeroLocus (J : Set A) = ∅ :=
  support_preimage_empty_of_radical_isUnit (algebraMap A B) J p hp
    (IsLocalization.Away.algebraMap_isUnit p)

/-- 概要：中心局所化を経由する任意のスキーム射上で閉台の逆像は空（論文 (3.6)）。
方針：指定された因数分解を点で評価し、局所化の素点での空性へ戻す。
規約：スキームは非アフィンでもよく、指定された射を保持する。
使われ方：Y = S, X とその底変換における支持条件の消滅。 -/
theorem scheme_support_preimage_empty_after_inversion (J : Ideal A) (p : A)
    {R : Type u} [CommRing R] [Algebra A R] [IsLocalization.Away p R]
    (hp : p ∈ J.radical) {Y V : Scheme.{u}} (f : Y ⟶ Spec (.of A))
    (g : V ⟶ Y) (h : V ⟶ Spec (.of R))
    (comm : g ≫ f = h ≫ Spec.map (CommRingCat.ofHom (algebraMap A R))) :
    g ⁻¹' (f ⁻¹' PrimeSpectrum.zeroLocus (J : Set A)) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have he : f (g x) = PrimeSpectrum.comap (algebraMap A R) (h x) :=
    congrArg (fun a ↦ a x) comm
  have hx' : h x ∈ PrimeSpectrum.comap (algebraMap A R) ⁻¹'
      PrimeSpectrum.zeroLocus (J : Set A) := by
    change f (g x) ∈ PrimeSpectrum.zeroLocus (J : Set A) at hx
    change PrimeSpectrum.comap (algebraMap A R) (h x) ∈ PrimeSpectrum.zeroLocus (J : Set A)
    exact he ▸ hx
  exact Set.eq_empty_iff_forall_notMem.mp
    (support_preimage_empty_after_inversion (B := R) J p hp) (h x) hx'

end SerrePositivity.KST.Descent
