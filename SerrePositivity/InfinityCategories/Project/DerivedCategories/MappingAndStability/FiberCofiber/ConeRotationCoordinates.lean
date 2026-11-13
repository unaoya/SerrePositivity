module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.CofiberFiberRotation

/-! # Cone の回転同値の成分

概要：回転同値の二射影と逆シフトによる次数移送を計算する。
方針：cone の lift の成分公式で符号を照合する。
規約：全整数次数。使われ方：D7 の明示的比較との一致。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
open CochainComplex HomComplex
set_option backward.isDefEq.respectTransparency false
universe u
variable {S : Type u} [CommRing S] {A B : _root_.SerrePositivity.DifferentialGraded.Complex S}
/-- 回転同値の第一座標は元の射のシフト。 -/
lemma coneRotation_fst_v (f : A ⟶ B) (p : ℤ) :
    (mappingCone.rotateHomotopyEquiv f).hom.f (p-1) ≫
      (mappingCone.fst (mappingCone.inr f)).val.v (p-1) p (by omega) =
    (A.shiftFunctorObjXIso 1 (p-1) p (by omega)).hom ≫ f.f p := by
  calc
    _ = (-(Cocycle.ofHom f).leftShift 1 1 (zero_add 1)).val.v (p-1) p (by omega) :=
      mappingCone.lift_f_fst_v _ _ _ _ _ _ _
    _ = _ := by
      simp only [Cocycle.coe_neg, Cocycle.leftShift_coe, Cocycle.ofHom_coe, Cochain.neg_v]
      rw [Cochain.leftShift_v _ 1 1 (zero_add 1) (p-1) p (by omega) p (add_zero p)]
      norm_num [Cochain.ofHom_v]
/-- 回転同値の第二座標は cone ホモトピーの負のシフト。 -/
lemma coneRotation_snd_v (f : A ⟶ B) (p : ℤ) :
    (mappingCone.rotateHomotopyEquiv f).hom.f (p-1) ≫
      (mappingCone.snd (mappingCone.inr f)).v (p-1) (p-1) (add_zero _) =
    -((A.shiftFunctorObjXIso 1 (p-1) p (by omega)).hom ≫
      (mappingCone.inl f).v p (p-1) (by omega)) := by
  calc
    _ = (-(mappingCone.inl f).leftShift 1 0 (neg_add_cancel 1)).v (p-1) (p-1) (add_zero _) :=
      mappingCone.lift_f_snd_v _ _ _ _ _ _ _
    _ = _ := by
      simp only [Cochain.neg_v]
      rw [Cochain.leftShift_v _ 1 0 (neg_add_cancel 1) (p-1) (p-1) (add_zero _) p (by omega)]
      norm_num
/-- 逆向きの二重シフトと成分の次数移送は打ち消し合う。 -/
lemma inverseDoubleShift_comp_XIso (p : ℤ) :
    ((shiftFunctorCompIsoId (_root_.SerrePositivity.DifferentialGraded.Complex S) (1 : ℤ) (-1) (by omega)).inv.app A).f p ≫
      (A.shiftFunctorObjXIso 1 (p-1) p (by omega)).hom = 𝟙 (A.X p) := by
  simp [shiftFunctorCompIsoId, shiftFunctorAdd'_hom_app_f', shiftFunctorZero_inv_app_f,
    CochainComplex.shiftFunctorObjXIso]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
