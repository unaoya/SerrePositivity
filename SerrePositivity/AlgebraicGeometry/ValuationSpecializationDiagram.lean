module

public import SerrePositivity.AlgebraicGeometry.ValuationProbeExtension
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
概要：スキームの点の特殊化を、一般点の剰余体の付値部分環で実現する。
方針：閉じた側の stalk から一般点の剰余体への射を、局所的な付値部分環へ因子化する。
規約：Noether 性・有限型を仮定しない。
使われ方：G1 の v 判定から特殊化の鎖を持ち上げる構成。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry IsLocalRing
universe u

/-- 一つの特殊化を、同じ剰余体の付値部分環からの射で実現する。 -/
theorem exists_valuation_specialization_diagram (Y : Scheme.{u}) {p q : Y} (h : p ⤳ q) :
    ∃ (W : ValuationSubring (Y.residueField p))
      (k : Spec (CommRingCat.of W) ⟶ Y),
      k (closedPoint W) = q ∧
        Spec.map (CommRingCat.ofHom (algebraMap W (Y.residueField p))) ≫ k =
          Y.fromSpecResidueField p := by
  let a := Y.presheaf.stalkSpecializes h ≫ Y.residue p
  obtain ⟨W, hW, hb⟩ := IsLocalRing.exists_factor_valuationRing a.hom
  let b : Y.presheaf.stalk q →+* W := a.hom.codRestrict W.toSubring hW
  letI : IsLocalHom b := hb
  let k := Spec.map (CommRingCat.ofHom b) ≫ Y.fromSpecStalk q
  refine ⟨W, k, ?_, ?_⟩
  · change Y.fromSpecStalk q (Spec.map (CommRingCat.ofHom b) (closedPoint W)) = q
    have hc : Spec.map (CommRingCat.ofHom b) (closedPoint W) =
        closedPoint (Y.presheaf.stalk q) := comap_closedPoint b
    rw [hc, Y.fromSpecStalk_closedPoint]
  · change Spec.map (CommRingCat.ofHom (algebraMap W (Y.residueField p))) ≫
      Spec.map (CommRingCat.ofHom b) ≫ Y.fromSpecStalk q = _
    rw [Scheme.fromSpecResidueField, ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk h]
    simp_rw [← Spec.map_comp_assoc]
    rfl

end SerrePositivity.AlgebraicGeometry
