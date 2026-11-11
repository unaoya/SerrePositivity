module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberRotationSign
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberTriangle
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ShiftAdditive
public import Mathlib.CategoryTheory.Triangulated.Rotate

/-! # Cofiber 三角形の回転同型

概要：回転長方形から得た cofiber 三角形は元の三角形の回転と同型である。
方針：最初の二射の幾何学的照合と第三接続射の負号を三角形同型にまとめる。
規約：既存の整数シフトを用いる。使われ方：distinguished triangle の回転への閉性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits Pretriangulated SSet
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

section
variable {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
local instance : Preadditive X.HomotopyCategory := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.preadditive_ho (X := X)

/-- 概要：回転列の第三射は一回シフトとの比較後も元の第一射の負のシフトとなる。
方針：懸垂に値を取る符号の式を一回シフトとの自然同型で移す。
規約：始点の厳密な等号による輸送を含める。使われ方：三角形同型の第三の可換式。 -/
lemma CofiberRotationRectangle.triangle_mor₃_eq_neg_shift {t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X}
    (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberRotationRectangle t) :
    r.suspensionSquare.suspensionFunctorObjIso.hom ≫
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle r.rotatedZeroTriangle r.rotated_isCofiber).mor₃ ≫
        (shiftFunctor (hoFunctor.obj X) (1 : ℤ)).map
          (eqToHom (congrArg SSet.HomotopyCategory.mk r.rotated_source)) =
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.shiftOneSuspensionIso X).inv.app t.hoShortComplex.X₁ ≫
        (-(shiftFunctor (hoFunctor.obj X) (1 : ℤ)).map t.hoShortComplex.f) := by
  have h := congrArg (fun f => f ≫
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.shiftOneSuspensionIso X).inv.app t.hoShortComplex.X₂)
    r.connecting_eq_neg_suspension
  calc
    _ = (r.suspensionSquare.suspensionFunctorObjIso.hom ≫
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting r.rotatedZeroTriangle r.rotated_isCofiber ≫
          (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctor X).map
            (eqToHom (congrArg SSet.HomotopyCategory.mk r.rotated_source))) ≫
              (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.shiftOneSuspensionIso X).inv.app t.hoShortComplex.X₂ := by
      change _ ≫ ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting r.rotatedZeroTriangle r.rotated_isCofiber ≫ _) ≫ _) = _
      simp only [Category.assoc]
      erw [← (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.shiftOneSuspensionIso X).inv.naturality
        (eqToHom (congrArg SSet.HomotopyCategory.mk r.rotated_source))]
      rfl
    _ = _ := h
    _ = _ := by
      rw [Preadditive.neg_comp, Preadditive.comp_neg]
      exact congrArg Neg.neg ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.shiftOneSuspensionIso X).inv.naturality t.hoShortComplex.f)

/-- 概要：回転長方形の右面の cofiber 三角形は元の cofiber 三角形の回転と同型。
方針：最初の二対象を等号で輸送し、最後を懸垂から一回シフトへ移す。
規約：第三の可換式には回転接続射の負号を使う。使われ方：TR2 の順方向。 -/
def CofiberRotationRectangle.triangleIsoRotate {t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X}
    (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t) (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberRotationRectangle t) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle r.rotatedZeroTriangle r.rotated_isCofiber ≅ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle t ht).rotate := by
  let e₁ := eqToIso (congrArg SSet.HomotopyCategory.mk r.rotated_source)
  let e₂ := eqToIso (congrArg SSet.HomotopyCategory.mk r.rotated_middle)
  let e₃ := r.suspensionSquare.suspensionFunctorObjIso.symm ≪≫
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.shiftOneSuspensionIso X).symm.app t.hoShortComplex.X₁
  refine Triangle.isoMk _ _ e₁ e₂ e₃ ?_ ?_ ?_
  · obtain ⟨hA, hB, hf⟩ := (Arrow.mk_eq_mk_iff _ _).mp r.rotated_f_arrow
    change r.rotatedZeroTriangle.hoShortComplex.f ≫ e₂.hom = e₁.hom ≫ t.hoShortComplex.g
    rw [hf]
    simp only [e₁, e₂, eqToIso.hom, Category.assoc, eqToHom_trans, eqToHom_refl,
      Category.comp_id]
  · obtain ⟨hA, hB, hf⟩ := (Arrow.mk_eq_mk_iff _ _).mp (r.rotated_g_arrow_connecting ht)
    change r.rotatedZeroTriangle.hoShortComplex.g ≫
      (r.suspensionSquare.suspensionFunctorObjIso.inv ≫ _) =
        e₂.hom ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting t ht ≫ _)
    calc
      _ = eqToHom hA ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnectingToSuspension t ht r.suspensionSquare ≫
          r.suspensionSquare.suspensionFunctorObjIso.inv) ≫
            (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.shiftOneSuspensionIso X).inv.app t.hoShortComplex.X₁ := by
        rw [hf]
        simp only [Category.assoc, eqToHom_refl, Category.id_comp]
        rfl
      _ = _ := by
        rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnectingToSuspension_comp_objIso_inv]
        rfl
  · change (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle r.rotatedZeroTriangle r.rotated_isCofiber).mor₃ ≫
      (shiftFunctor (hoFunctor.obj X) (1 : ℤ)).map e₁.hom =
        (r.suspensionSquare.suspensionFunctorObjIso.inv ≫ _) ≫ _
    apply (cancel_epi r.suspensionSquare.suspensionFunctorObjIso.hom).mp
    change r.suspensionSquare.suspensionFunctorObjIso.hom ≫
      ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle r.rotatedZeroTriangle r.rotated_isCofiber).mor₃ ≫
        (shiftFunctor (hoFunctor.obj X) (1 : ℤ)).map
          (eqToHom (congrArg SSet.HomotopyCategory.mk r.rotated_source))) =
      r.suspensionSquare.suspensionFunctorObjIso.hom ≫
        ((r.suspensionSquare.suspensionFunctorObjIso.inv ≫
          (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.shiftOneSuspensionIso X).inv.app t.hoShortComplex.X₁) ≫
            (-(shiftFunctor (hoFunctor.obj X) (1 : ℤ)).map t.hoShortComplex.f))
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using r.triangle_mor₃_eq_neg_shift

end
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
