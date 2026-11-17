module

public import SerrePositivity.AlgebraicGeometry.SchemeStructurePerfectCechPullback
public import SerrePositivity.AlgebraicGeometry.OpenCoverCechAugmentation

/-!
概要：実際の大域スカラーから、構造層の Frobenius 係数の増大写像を取る。
方針：既存の開被覆の増大写像に、同じスカラーの Frobenius 順極限を合成する。
規約：射影性・平坦性を仮定せず、元のスカラーと制限の射を保持する。
使われ方：F8 の基底・中心の増大写像を共通細分へ渡す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace Opposite _root_.AlgebraicGeometry
universe u
variable {R : Type u} [CommRing R] (Y : Scheme.{u}) (φ : R →+* Γ(Y, ⊤))
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)
variable (hY : ∀ O, (p : Y.presheaf.obj O) = 0)
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ]

/-- 実際のスカラーの Frobenius 順極限と、既存の開被覆の増大写像との合成。 -/
def schemeStructurePerfectCechAugmentation (U : ι → Y.Opens) :
    FrobeniusDirectLimit R p hp hR →ₗ[ℤ]
      (fullCechComplex (openCoverCechDiagram
        (frobeniusRingDiagram Y.presheaf p hp hY) U)).X 0 :=
  (openCoverCechAugmentation (frobeniusRingDiagram Y.presheaf p hp hY) U).comp
    (frobeniusDirectLimitMap p hp hR (hY (op ⊤)) φ).toAddMonoidHom.toIntLinearMap

set_option backward.isDefEq.respectTransparency false in
/-- スカラーからの増大写像は、Čech 複体のサイクルに入る。 -/
theorem schemeStructurePerfectCechAugmentation_cycle (U : ι → Y.Opens) :
    ((fullCechComplex (openCoverCechDiagram
      (frobeniusRingDiagram Y.presheaf p hp hY) U)).d 0 1).hom.comp
        (schemeStructurePerfectCechAugmentation Y φ p hp hR hY U) = 0 := by
  change (fullCechDifferential (openCoverCechDiagram
    (frobeniusRingDiagram Y.presheaf p hp hY) U) 1).comp
      ((openCoverCechAugmentation (frobeniusRingDiagram Y.presheaf p hp hY) U).comp _) = 0
  rw [← LinearMap.comp_assoc, openCoverCechAugmentation_squared, LinearMap.zero_comp]

set_option backward.isDefEq.respectTransparency false in
/-- 実際の被覆の細分は、同じ大域スカラーからの増大写像を保つ。 -/
theorem schemeStructurePerfectCechAugmentation_refinement
    (U : ι → Y.Opens) (V : κ → Y.Opens) (ρ : κ → ι)
    (hρ : ∀ j, V j ≤ U (ρ j)) :
    ((openCoverCechRefinementMap (frobeniusRingDiagram Y.presheaf p hp hY)
      U V ρ hρ).f 0).hom.comp (schemeStructurePerfectCechAugmentation Y φ p hp hR hY U) =
        schemeStructurePerfectCechAugmentation Y φ p hp hR hY V := by
  change (openCoverCechRefinementCochains (frobeniusRingDiagram Y.presheaf p hp hY)
    U V ρ hρ 1).comp
      ((openCoverCechAugmentation (frobeniusRingDiagram Y.presheaf p hp hY) U).comp _) = _
  rw [← LinearMap.comp_assoc, openCoverCechRefinement_augmentation]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- 各長さ一タプルでは、元のスカラーと制限の合成の Frobenius 順極限。 -/
theorem schemeStructurePerfectCechAugmentation_apply
    (U : ι → Y.Opens) (x : FrobeniusDirectLimit R p hp hR) (t : Fin 1 → ι) :
    schemeStructurePerfectCechAugmentation Y φ p hp hR hY U x t =
      frobeniusDirectLimitMap p hp hR
        (hY (op (cechOpenIntersection U (cechTupleSupport t))))
        (((Y.presheaf.map (homOfLE (show
          cechOpenIntersection U (cechTupleSupport t) ≤ ⊤ from le_top)).op).hom).comp φ) x := by
  exact congrArg (fun m ↦ m x)
    (frobeniusDirectLimitMap_comp p hp hR (hY (op ⊤)) φ
      (hY (op (cechOpenIntersection U (cechTupleSupport t))))
      (Y.presheaf.map (homOfLE (show
        cechOpenIntersection U (cechTupleSupport t) ≤ ⊤ from le_top)).op).hom)

end SerrePositivity.AlgebraicGeometry
