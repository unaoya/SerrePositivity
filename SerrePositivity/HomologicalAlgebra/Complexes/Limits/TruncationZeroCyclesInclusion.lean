module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ExtendedTruncationRestriction

/-!
# 元の延長切断包含と既存の cycles 包含の一致

概要：同じ切断の零次数直接評価は元の cycles 同型と包含を合成した射である。
方針：元の restriction 成分と cycles/opcycles 同型を相殺する。
規約：元の切断・包含・cycles 同型を保つ。
使われ方：元の Γ 零次数像と標準閉恒等辺の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

lemma truncLE'ToRestriction_cycles (H : Complex A)
    (e : (ComplexShape.down ℕ).Embedding (ComplexShape.up ℤ)) [e.IsTruncLE]
    {n : ℕ} {i : ℤ} (hi : e.f n = i) (hb : e.BoundaryLE n) :
    (H.truncLE'ToRestriction e).f n ≫ (H.restrictionXIso e hi).hom =
      (H.truncLE'XIsoCycles e hi hb).hom ≫ H.iCycles i := by
  have hb' : e.op.BoundaryGE n := by simpa using hb
  have h := H.op.restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv e.op hi hb'
  have h' := congrArg Quiver.Hom.unop h
  change (H.truncLE'ToRestriction e).f n =
    (H.op.truncGE'XIsoOpcycles e.op hi hb').inv.unop ≫
      (H.op.pOpcycles i).unop ≫ (H.op.restrictionXIso e.op hi).hom.unop at h'
  have hXi : (H.op.restrictionXIso e.op hi).hom.unop = (H.restrictionXIso e hi).inv := by
    subst i
    rfl
  have hc : H.op.pOpcycles i ≫ (H.opcyclesOpIso i).hom = (H.iCycles i).op :=
    (H.sc i).op_pOpcycles_opcyclesOpIso_hom
  have hc' : (H.opcyclesOpIso i).hom.unop ≫ (H.op.pOpcycles i).unop = H.iCycles i :=
    congrArg Quiver.Hom.unop hc
  have hp : (H.op.pOpcycles i).unop = (H.opcyclesOpIso i).unop.inv ≫ H.iCycles i := by
    apply (Iso.eq_inv_comp (H.opcyclesOpIso i).unop).mpr
    exact hc'
  rw [h', Category.assoc, Category.assoc, hXi, Iso.inv_hom_id, Category.comp_id, hp]
  rfl

lemma truncationExtendedZeroInclusion_cycles
    (e : (ComplexShape.down ℕ).Embedding (ComplexShape.up ℤ))
    (he : e = ComplexShape.embeddingUpIntLE 0) (hz : e.f 0 = (0 : ℤ)) (H : Complex A) :
    _root_.SerrePositivity.ComplexLimits.truncationExtendedZeroInclusion A e he hz H =
    (H.truncLE'XIsoCycles (ComplexShape.embeddingUpIntLE 0)
      (show (ComplexShape.embeddingUpIntLE 0).f 0 = (0 : ℤ) by simp)
      ((ComplexShape.boundaryLE_embeddingUpIntLE_iff 0 0).mpr rfl)).hom ≫ H.iCycles 0 := by
  subst e
  exact (_root_.SerrePositivity.ComplexLimits.extendedTruncationInclusion_restriction H (ComplexShape.embeddingUpIntLE 0) hz).trans
    (_root_.SerrePositivity.ComplexLimits.truncLE'ToRestriction_cycles A H (ComplexShape.embeddingUpIntLE 0) hz
      ((ComplexShape.boundaryLE_embeddingUpIntLE_iff 0 0).mpr rfl))

end SerrePositivity.ComplexLimits
