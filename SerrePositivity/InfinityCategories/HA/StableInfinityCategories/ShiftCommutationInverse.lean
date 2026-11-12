module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ShiftCommutationMonoid

/-! # 反対次数のシフト交換同型

概要：次数 a の交換同型から次数 -a の交換同型を作る。
方針：二つのシフト自己同値の単位・余単位で逆同型を挟む。
規約：交換同型の符号はシフトの次数を表す。使われ方：一回シフトの比較の整数冪。
-/
@[expose] public section
noncomputable section
universe v u v' u'
open CategoryTheory Functor
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [HasShift C ℤ] [HasShift D ℤ] {F : C ⥤ D}

/-- 概要：反対次数のシフトとの交換同型。
方針：像側で a と -a を挿入し、交換同型を逆に使い、始域で -a と a を消す。
規約：任意の整数 a。使われ方：次数付き交換同型モノイドの逆元。 -/
def stableShiftCommutationNeg {a : ℤ} (e : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableShiftCommutationIso F a) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableShiftCommutationIso F (-a) :=
  (Functor.rightUnitor _).symm ≪≫
    isoWhiskerLeft (shiftFunctor C (-a) ⋙ F)
      (shiftFunctorCompIsoId D a (-a) (add_neg_cancel a)).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight
      (Functor.associator _ _ _ ≪≫ isoWhiskerLeft (shiftFunctor C (-a)) e.symm ≪≫
        (Functor.associator _ _ _).symm) (shiftFunctor D (-a)) ≪≫
    isoWhiskerRight
      (isoWhiskerRight (shiftFunctorCompIsoId C (-a) a (neg_add_cancel a)) F ≪≫
        Functor.leftUnitor F) (shiftFunctor D (-a))

/-- 概要：反対次数の交換同型の成分は単位・逆比較・余単位の合成。
方針：自然同型の合成と whiskering を展開する。
規約：合成の順序を固定する。使われ方：逆元の計算。 -/
lemma stableShiftCommutationNeg_hom_app {a : ℤ} (e : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableShiftCommutationIso F a)
    (X : C) :
    (stableShiftCommutationNeg e).hom.app X =
      (shiftFunctorCompIsoId D a (-a) (add_neg_cancel a)).inv.app
          (F.obj ((shiftFunctor C (-a)).obj X)) ≫
        (shiftFunctor D (-a)).map (e.inv.app ((shiftFunctor C (-a)).obj X)) ≫
        (shiftFunctor D (-a)).map
          (F.map ((shiftFunctorCompIsoId C (-a) a (neg_add_cancel a)).hom.app X)) := by
  simp [stableShiftCommutationNeg]

/-- 概要：次数 a の比較と反対次数の比較を合成すると標準の零次数の比較になる。
方針：シフト自己同値の三角恒等式と交換同型の自然性で単位・余単位を消す。
規約：次数の和 a + (-a) = 0 に沿う合成。使われ方：整数冪のための右逆元。 -/
lemma stableShiftCommutation_mul_neg {a : ℤ} (e : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableShiftCommutationIso F a) :
    Functor.CommShift.isoAdd' (add_neg_cancel a) e (stableShiftCommutationNeg e) =
      Functor.CommShift.isoZero F ℤ := by
  ext X
  have hn := e.hom.naturality ((shiftFunctorCompIsoId C a (-a) (add_neg_cancel a)).hom.app X)
  dsimp at hn
  have hc := shift_shiftFunctorCompIsoId_hom_app (C := C) a (-a) (add_neg_cancel a) X
  simp only [Functor.CommShift.isoAdd'_hom_app, stableShiftCommutationNeg_hom_app,
    Functor.CommShift.isoZero_hom_app, Functor.comp_obj, Category.assoc]
  rw [← hc]
  simp_rw [← Functor.map_comp_assoc]
  rw [hn]
  simp only [Iso.inv_hom_id_app_assoc]
  have hd := (shiftFunctorCompIsoId D a (-a) (add_neg_cancel a)).inv.naturality
    (F.map ((shiftFunctorCompIsoId C a (-a) (add_neg_cancel a)).hom.app X))
  dsimp at hd
  rw [← reassoc_of% hd]
  simp only [shiftFunctorCompIsoId, Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app,
    Iso.symm_hom, Iso.symm_inv, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app_assoc, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
