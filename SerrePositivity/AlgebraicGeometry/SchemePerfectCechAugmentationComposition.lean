module

public import SerrePositivity.AlgebraicGeometry.SchemeStructurePerfectCechAugmentation

/-!
概要：スカラーの合成は、実際の Frobenius 係数の増大写像の合成になる。
方針：既存の増大写像に合成した環の Frobenius 写像の合成則を使う。
規約：同じ大域スカラーと被覆を保持する。
使われ方：閉中心の商の辺と増大写像の可換性。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace Opposite _root_.AlgebraicGeometry
universe u
variable {R S : Type u} [CommRing R] [CommRing S]
variable {ι : Type} [LinearOrder ι]

set_option backward.isDefEq.respectTransparency false in
/-- 実際のスカラーの合成は、同じ増大写像と Frobenius の係数写像の合成になる。 -/
theorem schemeStructurePerfectCechAugmentation_comp
    (Y : Scheme.{u}) (φ : S →+* Γ(Y, ⊤)) (q : R →+* S)
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hS : (p : S) = 0)
    (hY : ∀ O, (p : Y.presheaf.obj O) = 0) (U : ι → Y.Opens) :
    schemeStructurePerfectCechAugmentation Y (φ.comp q) p hp hR hY U =
      (schemeStructurePerfectCechAugmentation Y φ p hp hS hY U).comp
        (frobeniusDirectLimitMap p hp hR hS q).toAddMonoidHom.toIntLinearMap := by
  apply LinearMap.ext
  intro x
  change (openCoverCechAugmentation (frobeniusRingDiagram Y.presheaf p hp hY) U)
      (frobeniusDirectLimitMap p hp hR (hY (op ⊤)) (φ.comp q) x) =
    (openCoverCechAugmentation (frobeniusRingDiagram Y.presheaf p hp hY) U)
      (frobeniusDirectLimitMap p hp hS (hY (op ⊤)) φ
        (frobeniusDirectLimitMap p hp hR hS q x))
  congr 1
  exact (congrArg (fun m ↦ m x)
    (frobeniusDirectLimitMap_comp p hp hR hS q (hY (op ⊤)) φ)).symm

end SerrePositivity.AlgebraicGeometry
