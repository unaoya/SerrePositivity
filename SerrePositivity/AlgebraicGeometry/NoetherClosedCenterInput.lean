module

public import SerrePositivity.AlgebraicGeometry.NoetherClosedCenterImage
public import SerrePositivity.AlgebraicGeometry.NoetherClosedPerfectCechProperty
public import SerrePositivity.AlgebraicGeometry.SchemeBlowupProper

/-!
概要：真に小さい中心像にNoether帰納の仮定を適用する。
方針：中心の閉埋め込みを元の閉埋め込みに合成し、同じ固有全射を底変換する。
規約：中心の厚みと元のブローアップを保持する。
使われ方：閉像の帰納（承認済み計画I09）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
set_option backward.isDefEq.respectTransparency false

/-- 中心像の厳密な降下により、中心上の元の射の普遍Čech降下を得る。 -/
theorem noetherClosed_center_input
    {R : Type u} [CommRing R] [IsNoetherianRing R] (p : ℕ) (hp : p.Prime)
    (C : TopologicalSpace.Closeds (Spec (CommRingCat.of R)))
    (ih : ∀ D < C, NoetherClosedPerfectCechProperty (Spec (CommRingCat.of R)) p hp D)
    {Y : Scheme.{u}} (j : Y ⟶ Spec (CommRingCat.of R)) [IsClosedImmersion j]
    [Nonempty Y] (hj : Set.range j = (C : Set (Spec (CommRingCat.of R))))
    (J : Y.IdealSheafData) (hJ : Dense (centerComplement J).carrier)
    [Surjective (blowupπ J)] :
    PerfectCechUniversalDescent p hp (pullback.snd (blowupπ J) J.subschemeι) := by
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian j
  have h := ih (closedCenterImage j J) (closedCenterImage_lt j C hj J hJ)
  apply h J.subscheme (J.subschemeι ≫ j) inferInstance
  · change Set.range (j ∘ J.subschemeι) = j '' (J.support : Set Y)
    rw [Set.range_comp, J.range_subschemeι]
  · exact inferInstance
  · exact inferInstance

end SerrePositivity.AlgebraicGeometry
