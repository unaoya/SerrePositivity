module

public import SerrePositivity.CLMST.PerfectoidizationIsogeny.GeneralRank
public import SerrePositivity.CLMST.PerfectoidizationIsogeny.Rank.ClosedSides
public import SerrePositivity.CommutativeAlgebra.Localization.Away
public import SerrePositivity.BhattScholze.Perfectoidization.Excision
public import SerrePositivity.BhattScholze.Perfectoidization.FiniteComparisonExcision

/-! # Prop 2.4.7 の証明

## 概要

有限・有限表示な `S` の perfectoid 化への標準写像の錐は、エタールな主開集合の外に台を持つ（`isogeny_of_specified`）。標準 perfectoid 化に特殊化して CLMST Prop 2.4.7（`proposition_2_4_7`）を得る。

## 方針

実際の階数の図式と定数階数の有限比較に BS Cor 8.12 の環の系（`BhattScholze.klFiniteComparisonExcision_of_perfectoid`）を当て、導来完備性と付値環への一意な延長を供給して、指定した普遍単位の四角を保ったまま降下する。原典の Rem 2.4.6（Σ_r のガロア閉包）の代わりに、Zariski 局所的な分解と Cor 8.12 を使う。

## 規約

CLMST Prop 2.4.7。外部の入力は BS Thm 1.17(1) と Cor 8.12 の既存の宣言だけ。旧 `CLMST/Prop247Proof`（`prop247_` を外し、`proposition_2_4_7_proved` を `proposition_2_4_7` に改名した。旧入口 `Inputs.proposition_2_4_7` は削除）。

## 使われ方

`Consequences`、Paper（Theorem 2.5 の混標数）。
-/

@[expose] public noncomputable section

universe u

section Prop247ProofPart

namespace SerrePositivity.CLMST
open DerivedCompletion
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/--
## 概要
有限・有限表示な S の指定 perfectoid 化への錐は、エタールな主開集合の補集合に支持される。
## 方針
実 rank データを選び、完備性と付値環への一意延長から BS excision を供給して元の錐へ降下する。
## 規約
有界 p 冪ねじれは既存の完備底変換に用い、指定した f の変更はしない。
## 使われ方
標準 perfectoid 化に特殊化して Prop 2.4.7 を証明する。
-/
theorem isogeny_of_specified
    (R S C : Type u) [CommRing R] [CommRing S] [CommRing C]
    [Algebra R S] [Algebra R C] [Module.Finite R S] [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (f : S →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom)
    (hbounded : ∃ N : ℕ, ∀ n : ℕ, ∀ s : S,
      (p : S) ^ n * s = 0 → (p : S) ^ N * s = 0)
    (g : R) (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g))) :
    ∃ N : ℕ, moduleMapConeScalar R f.toLinearMap (g ^ N) = 0 := by
  obtain ⟨B, hB, hAIC, _hflat, P, β, hβ, t, ht, T, u, hu, Q, γ, hγ,
    hProduct, hdescent⟩ := exists_canonical_generalRank_descent_data R S C p hR
      (fun B _ hB _ => BhattScholze.klFiniteComparisonExcision_of_perfectoid B p hB) f hf hbounded g hetale
  let hetaleB := etaleAway_tensor_baseChange (R := R) (A := S) (B := B) g hetale
  let (n : t) : Algebra
      (rankSourceImage B (B ⊗[R] S) (algebraMap R B g) hetaleB n) (T n) :=
    (u n).toRingHom.toAlgebra
  let (n : t) : IsScalarTower B
      (rankSourceImage B (B ⊗[R] S) (algebraMap R B g) hetaleB n) (T n) :=
    IsScalarTower.of_algHom (u n)
  have hT (n : t) : IsIntegralPerfectoid (T n) p := (hu n).1
  obtain ⟨hA, hX, hI, _⟩ := rankSource_closedSide_completeness
    B (B ⊗[R] S) p hB (algebraMap R B g) (fun n => T n) hT
  have hPB : BhattScholze.KLCanonicalExcisionSquare hβ hProduct
      (rankTensorUnit B (B ⊗[R] S) (fun n => T n)) (algebraMap R B g) := by
    apply BhattScholze.klCanonicalExcisionSquare_of_excision B p hB
      (B ⊗[R] S) ((n : t) → T n ⊗[B] (B ⊗[R] S)) P ((n : t) → Q n)
      (rankTensorUnit B (B ⊗[R] S) (fun n => T n)) (algebraMap R B g)
      β (rankProductUnit B (B ⊗[R] S) (fun n => T n) (fun n => Q n) γ)
      hβ hProduct hA hX hI
    intro V _ _ _ _ _ k hk
    let : Algebra (B ⊗[R] S) V := k.toAlgebra
    have hg : k (algebraMap B (B ⊗[R] S) (algebraMap R B g)) ≠ 0 := by
      simpa only [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker] using hk
    exact aic_rankSourceProduct_valuation_extension B (B ⊗[R] S) p hB hAIC
      (algebraMap R B g) hetaleB t ht (fun n => T n) hu V hg
  obtain ⟨N, hN, _⟩ := hdescent hPB
  exact ⟨N, hN⟩

/--
## 概要
CLMST Prop 2.4.7：標準 perfectoid 化への実導来錐は J-isogeny である。
## 方針
各 g の主開集合でのエタール性に指定単位版の降下定理を適用する。
## 規約
文献入力と同じ署名を保ち、有界ねじれ以外の追加仮定を置かない。
## 使われ方
CLMST.proposition_2_4_7 の証明と専用依存監査の公開入口である。
-/
theorem proposition_2_4_7
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (J : Ideal R) (hJ : J.FG)
    (hEtale : ∀ g ∈ J, let _ := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g)))
    (hbounded : ∃ N : ℕ, ∀ (n : ℕ) (s : S),
      (p : S) ^ n * s = 0 → (p : S) ^ N * s = 0) :
    ∀ g ∈ J, ∃ N : ℕ,
      moduleMapConeScalar R (BhattScholze.perfectoidizationModuleMap R S p hR) (g ^ N) = 0 := by
  clear hJ
  intro g hg
  exact isogeny_of_specified R S (Perfectoidization R S p hR) p hR
    (IsScalarTower.toAlgHom R S (Perfectoidization R S p hR))
    (isPerfectoidization_toPerfectoidization R S p hR) hbounded g (hEtale g hg)

end SerrePositivity.CLMST

end Prop247ProofPart
