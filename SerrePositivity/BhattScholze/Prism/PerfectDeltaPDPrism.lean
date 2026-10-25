module

public import SerrePositivity.BhattScholze.Prism.PerfectDeltaPDCompletion
public import SerrePositivity.BhattScholze.Prism.PerfectOrientedPrism
public import SerrePositivity.BhattScholze.Delta.DistinguishedQuotientComplete

/-! # 完全δ環のdistinguished元による実完備化の完全prism

実H⁰の完全δ性からp正則性を供給し、導来/古典的比較とLemma 2.34で
生成元の正則性を証明する。F5で商のp完備性も供給する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 完全δ環とdistinguished元から、実PD完備化H⁰上の具体的な完全prismを構成する。 -/
def perfectDeltaPDPrism (D : DeltaStructure p A) (hD : D.IsPerfect) (d : A)
    (hd : D.IsDistinguished d) :
    letI := pdCompletionCommRing A p d
    OrientedPrism p (PDCompletionH0 A p d) := by
  letI := pdCompletionCommRing A p d
  let H := PDCompletionH0 A p d
  let DH := deltaPDCompletionStructure D d
  let j := pdCompletionUnit A p d
  have hH := deltaPDCompletionStructure_isPerfect D hD d
  have hpH := pdCompletionH0_self_complete_p A p d
  have hdH := pdCompletionH0_self_complete_d A p d
  letI : IsAdicComplete (Ideal.span {(p : H)}) H :=
    (isRingModuleComplete_iff_isAdicComplete_natCast H p hH.p_mul_injective).mp hpH
  have hdist : DH.IsDistinguished (j d) := (pdCompletionUnit_isDeltaHom D d).map_isDistinguished hd
  exact OrientedPrism.ofDistinguished DH (j d) hdist (hH.distinguished_mul_injective hdist) hpH hdH

/-- 完全prismのδ構造は、実H⁰への一意延長δ構造そのもの。 -/
@[simp] theorem perfectDeltaPDPrism_deltaStructure
    (D : DeltaStructure p A) (hD : D.IsPerfect) (d : A) (hd : D.IsDistinguished d) :
    letI := pdCompletionCommRing A p d
    (perfectDeltaPDPrism D hD d hd).deltaStructure = deltaPDCompletionStructure D d := rfl

/-- 完全prismの選択生成元は元のdのKoszul標準像。 -/
@[simp] theorem perfectDeltaPDPrism_generator
    (D : DeltaStructure p A) (hD : D.IsPerfect) (d : A) (hd : D.IsDistinguished d) :
    letI := pdCompletionCommRing A p d
    (perfectDeltaPDPrism D hD d hd).generator = pdCompletionUnit A p d d := rfl

/-- 構成したprismのδ構造は完全。 -/
theorem perfectDeltaPDPrism_isPerfect
    (D : DeltaStructure p A) (hD : D.IsPerfect) (d : A) (hd : D.IsDistinguished d) :
    letI := pdCompletionCommRing A p d
    (perfectDeltaPDPrism D hD d hd).deltaStructure.IsPerfect :=
  deltaPDCompletionStructure_isPerfect D hD d

/-- 構成したprismの標準商は、pねじれを許して古典的p進完備。 -/
theorem perfectDeltaPDPrism_quotient_isAdicComplete
    (D : DeltaStructure p A) (hD : D.IsPerfect) (d : A) (hd : D.IsDistinguished d) :
    letI := pdCompletionCommRing A p d
    IsAdicComplete (Ideal.span {(p : PDCompletionH0 A p d ⧸
      Ideal.span {pdCompletionUnit A p d d})})
      (PDCompletionH0 A p d ⧸ Ideal.span {pdCompletionUnit A p d d}) := by
  let := pdCompletionCommRing A p d
  let P := perfectDeltaPDPrism D hD d hd
  have hP := perfectDeltaPDPrism_isPerfect D hD d hd
  let := P.isAdicComplete_p_of_perfect hP
  exact hP.distinguished_quotient_isAdicComplete
    ((pdCompletionUnit_isDeltaHom D d).map_isDistinguished hd)

end SerrePositivity.BhattScholze
