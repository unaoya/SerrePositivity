module

public import SerrePositivity.BhattScholze.Prism.Perfection.PerfectDeltaPDQuotientEquiv
public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismQuotientPerfectoid
public import SerrePositivity.BhattScholze.Delta.Perfect.WittDistinguished

/-! # B4-5：distinguished Witt商のperfectoid性の一般入口

実PD完備化後の商とp完備な標準商の比較を使い、Witt環のd完備性の仮定を除く。
標準Fontaine比較射自体の同型とは区別する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable (p : ℕ) [Fact p.Prime] (k : Type u) [CommRing k] [CharP k p] [PerfectRing k p]

/-- 完全係数環の任意のdistinguished Witt商はperfectoid。
台Witt環のd完備性、商のp正則性・非零性を要求しない。 -/
theorem wittDistinguishedQuotient_isIntegralPerfectoid
    (d : WittVector p k) (hd : (wittDeltaStructure p k).IsDistinguished d) :
    IsIntegralPerfectoid (WittVector p k ⧸ Ideal.span {d}) p := by
  let D := wittDeltaStructure p k
  have hD := wittDeltaStructure_isPerfect p k
  let T := WittVector p k ⧸ Ideal.span {d}
  let q := Ideal.Quotient.mk (Ideal.span {d})
  let := hD.distinguished_quotient_isAdicComplete hd
  let := pdCompletionCommRing (WittVector p k) p d
  obtain ⟨e, _⟩ := exists_perfectDeltaPDQuotientEquiv D hD d hd q
    Ideal.Quotient.mk_surjective Ideal.mk_ker
  have h := (perfectDeltaPDPrism D hD d hd).quotient_isIntegralPerfectoid
    (perfectDeltaPDPrism_isPerfect D hD d hd)
  exact isIntegralPerfectoid_of_ringEquiv p e h

end SerrePositivity.BhattScholze
