module

public import SerrePositivity.CLMST.PerfectoidizationIsogeny.Rank.Diagram
public import SerrePositivity.BhattScholze.Perfectoidization.FiniteComparisonExcision
public import SerrePositivity.BhattScholze.Semiperfectoid.Perfection.Product
public import SerrePositivity.BhattScholze.Perfectoidization.Interface.IntegralExistence

/-! # 階数の終域の比較と直積の普遍性

## 概要

成分の単位の直積が指定した perfectoid 化であるというデータを受け取り、元の比較を標準の誘導写像と同定し（`rankPerfectoidComparison_eq_canonical`）、標準 excision の下で核を制御する。元の有限な係数から直積の始域の整性を得て、成分の単位の直積の普遍性を示す。

## 方針

全体の単位を一つ選び、前段の指定した全体単位による証明（BhattScholze/Semiperfectoid/Perfection/Product）から直積の普遍性を得る。

## 規約

CLMST Prop 2.4.7。引き戻し性は明示的な仮定のまま。旧 `CLMST/Prop247RankTargetComparison`・`Prop247RankProductUniversality`。

## 使われ方

`GeneralRank`。
-/

@[expose] public noncomputable section

universe u

section Prop247RankTargetComparisonPart

namespace SerrePositivity.CLMST
open scoped _root_.TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    {ι : Type} [Finite ι] (T P : ι → Type u)
    [∀ i, CommRing (T i)] [∀ i, Algebra R (T i)]
    [∀ i, CommRing (P i)] [∀ i, Algebra R (P i)]
    (β : ∀ i, T i ⊗[R] S →ₐ[R] P i)

/-- 元の成分普遍単位の実直積写像。 -/
def rankProductUnit : ((i : ι) → T i ⊗[R] S) →ₐ[R] ((i : ι) → P i) :=
  AlgHom.pi (fun i => (β i).comp (Pi.evalAlgHom R (fun i => T i ⊗[R] S) i))

variable (p : ℕ) [Fact p.Prime] (C : Type u) [CommRing C] [Algebra R C]
    (f : S →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom)
    (hβ : ∀ i, IsPerfectoidization p (β i).toRingHom)
    (hProduct : IsPerfectoidization p (rankProductUnit R S T P β).toRingHom)

/-- 元の実 rank 終域比較は、元の直積単位による canonical 比較そのものである。 -/
theorem rankPerfectoidComparison_eq_canonical :
    rankPerfectoidComparison R S T p C f hf P β hβ =
      IsPerfectoidization.mapAlgHom hf hProduct (rankTensorUnit R S T) := by
  let η := rankProductUnit R S T P β
  let q := rankTensorUnit R S T
  let τ := rankPerfectoidComparison R S T p C f hf P β hβ
  have hτ : τ.comp f = η.comp q := by
    apply AlgHom.ext
    intro s
    exact LinearMap.congr_fun (rankPerfectoidComparison_square R S T p C f hf P β hβ) s
  obtain ⟨l, _hl, hu⟩ := hf.2 ((i : ι) → P i) hProduct.1 (η.comp q).toRingHom
  apply AlgHom.toRingHom_injective
  exact (hu τ.toRingHom (congrArg AlgHom.toRingHom hτ)).trans
    (hu (IsPerfectoidization.mapAlgHom hf hProduct q).toRingHom
      (congrArg AlgHom.toRingHom (IsPerfectoidization.mapAlgHom_comp hf hProduct q))).symm

/-- 元の canonical excision 四角形から、組立てで必要な実終域比較の核の零化を得る。
直積の普遍性と引き戻し性は実データとして指定し、Cor 8.12 は引用しない。 -/
theorem rankPerfectoidComparison_ker_of_canonical_excision
    (hR : IsIntegralPerfectoid R p) (g : R)
    (hPB : BhattScholze.KLCanonicalExcisionSquare hf hProduct (rankTensorUnit R S T) g) :
    ∀ x : (rankPerfectoidComparison R S T p C f hf P β hβ).toLinearMap.ker,
      g • x = 0 := by
  obtain ⟨hk, _hc⟩ := BhattScholze.perfectoidization_comparison_almost_of_canonical_excision hR hf hProduct
    (rankTensorUnit R S T) g hPB
  rw [rankPerfectoidComparison_eq_canonical R S T P β p C f hf hβ hProduct]
  exact hk g (_root_.SerrePositivity.BhattScholze.Almost.span_le_perfectoidIdeal R p hR g (Ideal.subset_span (Set.mem_singleton g)))

end SerrePositivity.CLMST

end Prop247RankTargetComparisonPart

section Prop247RankProductUniversalityPart

namespace SerrePositivity.CLMST
open scoped _root_.TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- 元の有限係数と各指定普遍単位から、実 rank 直積単位の普遍性を供給する。
直積単位の普遍性を追加仮定にせず、既存 B-I のみを存在選択に使用する。 -/
theorem rankProductUnit_isPerfectoidization_of_finite_coefficients
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    {ι : Type} [Finite ι] (T P : ι → Type u)
    [∀ i, CommRing (T i)] [∀ i, Algebra R (T i)] [∀ i, Module.Finite R (T i)]
    [∀ i, CommRing (P i)] [∀ i, Algebra R (P i)]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (β : ∀ i, T i ⊗[R] S →ₐ[R] P i)
    (hβ : ∀ i, IsPerfectoidization p (β i).toRingHom) :
    IsPerfectoidization p (rankProductUnit R S T P β).toRingHom := by
  letI : Module.Finite R ((i : ι) → T i ⊗[R] S) := inferInstance
  obtain ⟨C, hC, f, hf⟩ := BhattScholze.Inputs.exists_perfectoidization_of_integral R
    ((i : ι) → T i ⊗[R] S) p hR
  letI := hC
  change IsPerfectoidization p (_root_.SerrePositivity.BhattScholze.Semiperfectoid.productPerfectoidizationUnit
    (fun i => T i ⊗[R] S) P (fun i => (β i).toRingHom))
  exact _root_.SerrePositivity.BhattScholze.Semiperfectoid.productUnit_isPerfectoidization_of_specified (fun i => T i ⊗[R] S) P
    (fun i => (β i).toRingHom) p hβ C f hf

end SerrePositivity.CLMST

end Prop247RankProductUniversalityPart
