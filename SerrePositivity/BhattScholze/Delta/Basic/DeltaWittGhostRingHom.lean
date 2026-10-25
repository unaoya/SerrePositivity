module

public import SerrePositivity.BhattScholze.Delta.Basic.DeltaWittGhostLowCoefficients

/-! # ghost射単射下でのδからWittへの環射

全係数構成の環射性をghost射の単射性へ明示的に相対化する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- ghost射が単射なら、構成済み点ごとのWitt写像は環射。 -/
def deltaWittGhostRingHom (D : DeltaStructure p A)
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A)) :
    A →+* WittVector p A where
  toFun := deltaWittGhostVector D
  map_one' := by
    apply hg
    ext n
    simp only [WittVector.ghostMap_apply, map_one, deltaWittGhostVector_ghostComponent]
    change (D.frobeniusLift ^ n) 1 = 1
    exact map_one _
  map_mul' := by
    intro a b
    apply hg
    ext n
    simp only [WittVector.ghostMap_apply, map_mul,
      deltaWittGhostVector_ghostComponent]
    change (D.frobeniusLift ^ n) (a * b) = (D.frobeniusLift ^ n) a * (D.frobeniusLift ^ n) b
    exact map_mul _ _ _
  map_zero' := by
    apply hg
    ext n
    simp only [WittVector.ghostMap_apply, map_zero, deltaWittGhostVector_ghostComponent]
    change (D.frobeniusLift ^ n) 0 = 0
    exact map_zero _
  map_add' := by
    intro a b
    apply hg
    ext n
    simp only [WittVector.ghostMap_apply, map_add,
      deltaWittGhostVector_ghostComponent]
    change (D.frobeniusLift ^ n) (a + b) = (D.frobeniusLift ^ n) a + (D.frobeniusLift ^ n) b
    exact map_add _ _ _

/-- 構成した環射は第0係数環射の断面。 -/
theorem deltaWittGhostRingHom_constantCoeff_comp (D : DeltaStructure p A)
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A)) :
    WittVector.constantCoeff.comp (deltaWittGhostRingHom D hg) = RingHom.id A := by
  apply RingHom.ext
  intro a
  exact deltaWittGhostVector_coeff_zero D a

/-- p乗算単射下では、新しい全Witt環射の長さ2切り詰めは既存δ断面。 -/
theorem deltaWittGhostRingHom_truncate_two_comp (D : DeltaStructure p A)
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (hp : Function.Injective (fun a : A => (p : A) * a)) :
    (WittVector.truncate 2).comp (deltaWittGhostRingHom D hg) = D.sectionHom := by
  apply RingHom.ext
  intro a
  exact deltaWittGhostVector_truncate_two D hp a

/-- 全ghost成分を指定したWitt環射は、ghost射単射下で一意。 -/
theorem deltaWittGhostRingHom_unique (D : DeltaStructure p A)
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (f : A →+* WittVector p A)
    (hf : ∀ a n, WittVector.ghostComponent n (f a) = D.frobeniusLift^[n] a) :
    f = deltaWittGhostRingHom D hg := by
  apply RingHom.ext
  intro a
  apply hg
  funext n
  rw [WittVector.ghostMap_apply, WittVector.ghostMap_apply, hf]
  exact (deltaWittGhostVector_ghostComponent D a n).symm

end SerrePositivity.BhattScholze
