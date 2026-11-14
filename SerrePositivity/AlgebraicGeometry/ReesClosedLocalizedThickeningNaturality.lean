module

public import SerrePositivity.AlgebraicGeometry.ReesClosedLocalizedThickeningFrobenius
public import SerrePositivity.AlgebraicGeometry.ReesClosedRingThickeningNaturality
public import SerrePositivity.AlgebraicGeometry.ReesClosedRingNaturality
public import SerrePositivity.AlgebraicGeometry.ProjectiveLocalizedPowerNaturality

/-!
概要：実際の標準開の閉厚化 Frobenius は、厚さを下げる遷移と可換。
方針：商環の可換四角形を局所化の自然性へ渡す。
規約：元の厚さ n と m を、ともに p^e 倍した段を比較する。
使われ方：Rees の像の安定化に反復 Frobenius を接続する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (I : Ideal R) (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)

/-- 厚さを下げる実際の線形局所化の射と、厚化 Frobenius は可換。 -/
theorem reesClosedLocalizedThickeningFrobenius_transition
    (s : MvPolynomial ι R) (n m e : ℕ) (hmn : m ≤ n)
    (z : LocalizedModule (Submonoid.powers s) (A ⧸ (I ^ n).map (algebraMap R A))) :
    reesClosedLocalizedThickeningFrobenius I p hp hR hA s m e
      (IsLocalizedModule.map (Submonoid.powers s)
        (LocalizedModule.mkLinearMap (Submonoid.powers s) _)
        (LocalizedModule.mkLinearMap (Submonoid.powers s) _)
        (reesClosedRingTransition (ι := ι) I n m hmn).toLinearMap z) =
    IsLocalizedModule.map (Submonoid.powers s)
      (LocalizedModule.mkLinearMap (Submonoid.powers s) _)
      (LocalizedModule.mkLinearMap (Submonoid.powers s) _)
      (reesClosedRingTransition (ι := ι) I (p ^ e * n) (p ^ e * m)
        (Nat.mul_le_mul_left (p ^ e) hmn)).toLinearMap
      (reesClosedLocalizedThickeningFrobenius I p hp hR hA s n e z) := by
  apply projectiveLocalizedPowerMap_naturality
    (frobeniusDirectSystemMap R p hp hR 0 e (Nat.zero_le e))
    (reesClosedRingThickeningFrobenius I p hp hA n e)
    (reesClosedRingThickeningFrobenius I p hp hA m e) s (p ^ e)
    (reesClosedRingThickeningFrobenius_algebraMap I p hp hA n e s)
    (reesClosedRingThickeningFrobenius_algebraMap I p hp hA m e s)
    (reesClosedRingThickeningFrobenius_scalar I p hp hR hA n e)
    (reesClosedRingThickeningFrobenius_scalar I p hp hR hA m e)
  intro a
  exact (congrArg (fun f ↦ f a)
    (reesClosedRingThickeningFrobenius_transition I p hp hA n m e hmn)).symm

end SerrePositivity.AlgebraicGeometry
