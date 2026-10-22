module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovZeroClassMap
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovZeroLayerInverseComponents

/-!
概要：同じ零底・係数の実逆を shift した class 標的の実代数逆へ移す。
方針：係数の作用保存を shift し、元の四つの厳密三角形を対角直和にまとめる。
規約：元の底・係数逆を取り替えない。使われ方：後続段からの class 比較の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovZeroLayerInverse
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} {A B : Tower (NonpositiveAlgebra R)}
  {f : LevelHom A B} {i k : ℕ} {hi : i ≤ k}
  (e : PostnikovZeroLayerInverse R n f i k hi) (s : ℤ)

def shiftedClassMap : postnikovZeroClassTarget R (B.obj k).obj n s ⟶
    postnikovZeroClassTarget R (A.obj i).obj n s :=
  SquareZero.mapOver e.base _ _
    (DGBimoduleShift.mapOver e.base (postnikovLayerZeroBimodule R (A.obj i).obj n) s e.coefficient)

lemma shiftedClassMap_hom : (shiftedClassMap R e s).hom =
    biprod.map e.base.hom (e.coefficient.hom⟦s⟧') := by
  rw [shiftedClassMap, SquareZero.mapOver_hom, DGBimoduleShift.mapOver_hom]
  rfl

lemma shiftedClassMap_projection : shiftedClassMap R e s ≫ SquareZero.projection _ _ =
    SquareZero.projection _ _ ≫ e.base := SquareZero.mapOver_projection _ _ _ _

lemma shiftedClassMap_left : postnikovZeroClassMap R n s (f.app k).hom ≫
    shiftedClassMap R e s = postnikovZeroClassMap R n s (A.transition hi).hom := by
  apply Mon.Hom.ext
  change (postnikovZeroClassMap R n s (f.app k).hom).hom ≫
    (shiftedClassMap R e s).hom = (postnikovZeroClassMap R n s (A.transition hi).hom).hom
  rw [postnikovZeroClassMap_hom, shiftedClassMap_hom, postnikovZeroClassMap_hom,
    cochainBiprodMap_comp]
  have hb := congrArg Mon.Hom.hom e.left_base
  change (postnikovMap R (f.app k).hom 0).hom ≫ e.base.hom =
    (postnikovMap R (A.transition hi).hom 0).hom at hb
  have hc : (postnikovLayerMap R (f.app k).hom n)⟦s⟧' ≫ e.coefficient.hom⟦s⟧' =
      (postnikovLayerMap R (A.transition hi).hom n)⟦s⟧' :=
    ((shiftFunctor (Complex R) s).map_comp _ _).symm.trans
      (congrArg ((shiftFunctor (Complex R) s).map) e.left_coefficient)
  rw [hb, hc]
  rfl

lemma shiftedClassMap_right : shiftedClassMap R e s ≫
    postnikovZeroClassMap R n s (f.app i).hom = postnikovZeroClassMap R n s (B.transition hi).hom
    := by
  apply Mon.Hom.ext
  change (shiftedClassMap R e s).hom ≫ (postnikovZeroClassMap R n s (f.app i).hom).hom =
    (postnikovZeroClassMap R n s (B.transition hi).hom).hom
  rw [shiftedClassMap_hom, postnikovZeroClassMap_hom, postnikovZeroClassMap_hom,
    cochainBiprodMap_comp]
  have hb := congrArg Mon.Hom.hom e.right_base
  change e.base.hom ≫ (postnikovMap R (f.app i).hom 0).hom =
    (postnikovMap R (B.transition hi).hom 0).hom at hb
  have hc : e.coefficient.hom⟦s⟧' ≫ (postnikovLayerMap R (f.app i).hom n)⟦s⟧' =
      (postnikovLayerMap R (B.transition hi).hom n)⟦s⟧' :=
    ((shiftFunctor (Complex R) s).map_comp _ _).symm.trans
      (congrArg ((shiftFunctor (Complex R) s).map) e.right_coefficient)
  rw [hb, hc]
  rfl

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovZeroLayerInverse
