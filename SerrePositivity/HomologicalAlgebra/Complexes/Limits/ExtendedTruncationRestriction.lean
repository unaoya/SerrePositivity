module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ExtendOppositePoint

/-!
# 元の延長切断包含と同じ restriction の成分

概要：元の延長項同型で戻した切断包含は、同じ切断から restriction への射に一致する。
方針：同じ opposite 比較と元の liftExtend の成分式を相殺する。
規約：元の切断同型・包含・restriction を保つ。
使われ方：零次数の元の直接評価と cycles 包含の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded
variable {A : Type u} [CommRing A]

lemma extendedTruncationInclusion_restriction (H : Complex A)
    (e : (ComplexShape.down ℕ).Embedding (ComplexShape.up ℤ)) [e.IsTruncLE]
    {n : ℕ} {i : ℤ} (hi : e.f n = i) :
    ((H.truncLE' e).extendXIso e hi).inv ≫
      ((H.truncLEIso e).inv ≫ HomologicalComplex.ιTruncLE H e).f i =
    (H.truncLE'ToRestriction e).f n ≫ (H.restrictionXIso e hi).hom := by
  rw [HomologicalComplex.comp_f, ← Category.assoc, _root_.SerrePositivity.ComplexLimits.truncLEIso_inv_point]
  change ((H.op.truncGE' e.op).extendXIso e.op hi).hom.unop ≫
    ((H.op.πTruncGE e.op).f i).unop = _
  have h := e.op.liftExtend_f (H.op.restrictionToTruncGE' e.op)
    (H.op.restrictionToTruncGE'_hasLift e.op) hi
  change (H.op.πTruncGE e.op).f i = _ at h
  rw [h, unop_comp, unop_comp, ← Category.assoc]
  simp only [← Iso.unop_hom, ← Iso.unop_inv, Iso.hom_inv_id_assoc]
  have hXi : (H.op.restrictionXIso e.op hi).unop.inv = (H.restrictionXIso e hi).hom := by
    subst i
    rfl
  exact congrArg (fun f => ((H.op.restrictionToTruncGE' e.op).f n).unop ≫ f) hXi

end SerrePositivity.ComplexLimits
