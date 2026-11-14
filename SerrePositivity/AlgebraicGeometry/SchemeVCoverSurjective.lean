module

public import SerrePositivity.AlgebraicGeometry.SchemeVCoverComposition
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
概要：スキームの付値持ち上げから、その射の全射性を得る。
方針：各点の剰余体を試験環とし、持ち上げた付値環の閉点を取る。
規約：全射性から付値判定への逆向きは主張しない。
使われ方：G1 の subtrusive 判定と細分の点の持ち上げ。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
universe u

/-- スキームの付値判定を満たす射は全射。 -/
theorem IsSchemeVCover.surjective {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hf : IsSchemeVCover f) : Surjective f := by
  constructor
  intro y
  obtain ⟨W, hW, hval, e, l, _, hl⟩ := hf (Y.residueField y) (Y.fromSpecResidueField y)
  letI : IsDomain W := hW
  letI : ValuationRing W := hval
  refine ⟨l (IsLocalRing.closedPoint W), ?_⟩
  calc
    f (l (IsLocalRing.closedPoint W)) = (l ≫ f) (IsLocalRing.closedPoint W) := rfl
    _ = (Spec.map (CommRingCat.ofHom e) ≫ Y.fromSpecResidueField y)
        (IsLocalRing.closedPoint W) := congrArg (fun q ↦ q (IsLocalRing.closedPoint W)) hl
    _ = y := Y.fromSpecResidueField_apply y _

end SerrePositivity.AlgebraicGeometry
