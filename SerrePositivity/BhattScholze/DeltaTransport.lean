module

public import SerrePositivity.BhattScholze.WittTwoMap

/-! # 環同型によるδ構造の移送

W₂切断を環同型で共役し、元の環構造を変えずにδ構造を引き戻す。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-- 環同型の終域のδ構造を、W₂切断の共役によって始域へ引き戻す。 -/
def comapEquiv (E : DeltaStructure p B) (e : A ≃+* B) : DeltaStructure p A where
  sectionHom := (wittTwoMap e.symm.toRingHom).comp (E.sectionHom.comp e.toRingHom)
  coeff_zero := by
    intro x
    simp only [RingHom.comp_apply, wittTwoMap_coeff, E.coeff_zero]
    exact e.symm_apply_apply x

/-- 引き戻したδ写像は、環同型を通じた元のδ写像の共役。 -/
@[simp] theorem comapEquiv_delta (E : DeltaStructure p B) (e : A ≃+* B) (x : A) :
    (E.comapEquiv e).delta x = e.symm (E.delta (e x)) := by
  exact wittTwoMap_coeff e.symm.toRingHom (E.sectionHom (e x)) 1

/-- δ構造を引き戻す環同型はδ射。 -/
theorem comapEquiv_isDeltaHom (E : DeltaStructure p B) (e : A ≃+* B) :
    (E.comapEquiv e).IsDeltaHom E e.toRingHom := by
  intro x
  change e ((E.comapEquiv e).delta x) = E.delta (e x)
  rw [comapEquiv_delta]
  exact e.apply_symm_apply _

/-- 同じ環同型の逆も、引き戻したδ構造を保つ。 -/
theorem comapEquiv_symm_isDeltaHom (E : DeltaStructure p B) (e : A ≃+* B) :
    E.IsDeltaHom (E.comapEquiv e) e.symm.toRingHom :=
  (E.comapEquiv_isDeltaHom e).symm

end SerrePositivity.BhattScholze.DeltaStructure
