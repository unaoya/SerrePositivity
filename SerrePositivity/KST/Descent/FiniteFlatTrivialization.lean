module

public import SerrePositivity.KST.Descent.FiniteFlatRankCover
public import Mathlib.RingTheory.Localization.Free

/-!
# 有限平坦射の実際の有限自由な基本開自明化

## 概要
有限表示平坦加群を有限個の基本開で自由にし、忠実平坦な有限代数では正の有限基底を得る。

## 方針
素イデアルでの自由基底を一元局所化まで広げ、テンソル積への同型と単位イデアルの判定を使う。

## 規約
定 rank から自由性を結論せず、実際の局所基底を構成する。transfer の公式自体は別工程。

## 使われ方
論文 補題 3.2 のベクトル束の自明化と、正本 §13 決定 12 の局所 rank 公式への幾何入力。
-/

@[expose] public section

universe u v

open CategoryTheory AlgebraicGeometry Module
open scoped TensorProduct

namespace SerrePositivity.KST.Descent

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
  [Module.FinitePresentation R M] [Module.Flat R M]

/-- 概要：各素点の近傍の実際のテンソル積は自由で、その rank は元の stalk の rank（補題 3.2）。
方針：stalk の有限自由性を一元局所化へ広げ、局所化加群とテンソル積の実際の同型を使う。
規約：自由性と rank の一致を同時に返す。大域的な自由性を仮定しない。
使われ方：射影公式の束の作用を局所の整数 rank 倍へ移すための自明化。 -/
theorem exists_free_tensor_away_at_prime (p : PrimeSpectrum R) :
    ∃ r : R, r ∉ p.asIdeal ∧
      Module.Free (Localization.Away r) (Localization.Away r ⊗[R] M) ∧
      Module.finrank (Localization.Away r) (Localization.Away r ⊗[R] M) =
        Module.rankAtStalk M p := by
  have : Module.Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule.AtPrime p.asIdeal M) := Module.free_of_flat_of_isLocalRing
  obtain ⟨r, hr, hfree, hrank⟩ :=
    Module.FinitePresentation.exists_free_localizedModule_powers p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M) (Localization.AtPrime p.asIdeal)
  have := hfree
  let e := LocalizedModule.equivTensorProduct (Submonoid.powers r) M
  refine ⟨r, hr, Module.Free.of_equiv e, ?_⟩
  exact e.finrank_eq.symm.trans hrank

/-- 概要：有限表示平坦加群は単位イデアルを生成する有限個の基本開で実際に自由（補題 3.2）。
方針：各素点の局所自由化で全ての極大イデアルを避け、単位イデアルから有限部分族を選ぶ。
規約：各開部分は非空な素点を持ち、テンソル積の rank はその点での rank に一致する。
使われ方：有限 Zariski Čech 被覆に渡す実際の自由自明化。 -/
theorem exists_finite_free_tensor_cover :
    ∃ s : Finset R, Ideal.span (s : Set R) = ⊤ ∧
      ∀ r ∈ s, ∃ p : PrimeSpectrum R, r ∉ p.asIdeal ∧
        Module.Free (Localization.Away r) (Localization.Away r ⊗[R] M) ∧
        Module.finrank (Localization.Away r) (Localization.Away r ⊗[R] M) =
          Module.rankAtStalk M p := by
  classical
  let good : Set R := {r | ∃ p : PrimeSpectrum R, r ∉ p.asIdeal ∧
    Module.Free (Localization.Away r) (Localization.Away r ⊗[R] M) ∧
    Module.finrank (Localization.Away r) (Localization.Away r ⊗[R] M) =
      Module.rankAtStalk M p}
  have hspan : Ideal.span good = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := (Ideal.span good).exists_le_maximal hne
    have : m.IsMaximal := hm
    let p : PrimeSpectrum R := ⟨m, hm.isPrime⟩
    obtain ⟨r, hr, hfree, hrank⟩ := exists_free_tensor_away_at_prime R M p
    exact hr (hle (Ideal.subset_span (show r ∈ good from ⟨p, hr, hfree, hrank⟩)))
  obtain ⟨s, hsub, hs⟩ := (Ideal.span_eq_top_iff_finite good).mp hspan
  exact ⟨s, hs, fun r hr ↦ hsub hr⟩

variable (B : Type u) [CommRing B] [Algebra R B] [Module.Finite R B]
  [Module.Flat R B] [Module.FinitePresentation R B]

/-- 概要：有限忠実平坦な有限表示代数は有限基本開被覆で正の有限自由基底を持つ（補題 3.2）。
方針：実際の自由被覆と全射性による stalk rank の正値性から有限基底を選ぶ。
規約：各局所化代数は実際のテンソル積で、基底は Fin rank で添字付ける。
使われ方：有限平坦 transfer の射影公式と加法性から局所 rank 公式を証明する入力。 -/
theorem exists_positive_basis_tensor_cover
    [Surjective (Spec.map (CommRingCat.ofHom (algebraMap R B)))] :
    ∃ s : Finset R, Ideal.span (s : Set R) = ⊤ ∧
      ∀ r ∈ s, ∃ rank : ℕ, 0 < rank ∧
        Nonempty (Basis (Fin rank) (Localization.Away r) (Localization.Away r ⊗[R] B)) := by
  obtain ⟨s, hs, hfree⟩ := exists_finite_free_tensor_cover R B
  refine ⟨s, hs, ?_⟩
  intro r hr
  obtain ⟨p, hpr, hf, he⟩ := hfree r hr
  have := hf
  have : Nontrivial (Localization.Away r) :=
    (show Localization.Away r →+* Localization.AtPrime p.asIdeal from
      IsLocalization.map (M := .powers r) (T := p.asIdeal.primeCompl) _
        (RingHom.id _) (Submonoid.powers_le.mpr hpr)).domain_nontrivial
  have : AlgebraicGeometry.Flat (Spec.map (CommRingCat.ofHom (algebraMap R B))) :=
    AlgebraicGeometry.Flat.SpecMap_iff.mpr
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R B))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have hpos : 0 < Module.rankAtStalk B p := by
    rw [← Scheme.Hom.finrank_SpecMap_algebraMap R B p]
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one
      (((Spec.map (CommRingCat.ofHom (algebraMap R B))).one_le_finrank_iff_surjective.mpr
        inferInstance) p)
  refine ⟨Module.rankAtStalk B p, hpos, ?_⟩
  exact Eq.mp (congrArg (fun n ↦ Nonempty
    (Basis (Fin n) (Localization.Away r) (Localization.Away r ⊗[R] B))) he)
      ⟨Module.finBasis (Localization.Away r) (Localization.Away r ⊗[R] B)⟩

end SerrePositivity.KST.Descent
