module

public import SerrePositivity.AlgebraicGeometry.PrincipalRegularLift

/-!
概要：KST §5、Stacks 080Y の正則単項中心に沿う blowup の自明性。
方針：恒等係数写像の普遍持ち上げを構造射の逆射とし、分離性による一意性で逆性を示す。
規約：通常の Rees Proj を使い、環の整域性は仮定しない。
使われ方：可逆中心上の blowup の局所的な自明性と合成の比較。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
variable {R : Type u} [CommRing R] (I : Ideal R)
  (b : R) (hreg : b ∈ nonZeroDivisors R) (hI : I = Ideal.span {b})

set_option backward.isDefEq.respectTransparency false in
/--
概要：正則な単項中心の blowup は元のアフィンスキームと同型。
方針：恒等基底写像の正則単項持ち上げを逆射とする。
規約：KST §5、Stacks 080Y、順方向は実際の blowup の構造射。
使われ方：局所的に可逆な中心で blowup が変化しないことの入力。
-/
def affineBlowupPrincipalIso : affineBlowup I ≅ Spec (.of R) where
  hom := affineBlowupπ I
  inv := affineBlowupPrincipalRegularLift I (RingHom.id R) b hreg (by simpa using hI)
  hom_inv_id := by
    apply affineBlowup_hom_ext I (affineBlowupπ I)
      (affineBlowupπ_restrict_basicOpen_isIso I)
    · rw [Category.assoc, affineBlowupPrincipalRegularLift_base]
      simp
    · simp
  inv_hom_id := by
    rw [affineBlowupPrincipalRegularLift_base]
    change Spec.map (𝟙 (CommRingCat.of R)) = _
    exact Scheme.Spec.map_id _

include b hreg hI in
/--
概要：正則な単項中心では blowup の構造射は同型射。
方針：構造済みの同型の順射と同定する。
規約：KST §5、Stacks 080Y、追加公理を使わない。
使われ方：可逆中心の blowup の局所同型判定。
-/
theorem affineBlowupπ_isIso_of_regular_principal : IsIso (affineBlowupπ I) :=
  (affineBlowupPrincipalIso I b hreg hI).isIso_hom

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
