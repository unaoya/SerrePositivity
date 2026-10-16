module
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Whiskering

/-! # 同値による実現比較の成分計算 -/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u v' u'
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- 逆関手で戻してunitの逆を合成した射を送り直すと、counitによる自然な比較となる。 -/
lemma equivalence_map_inverse_then_unit (E : C ≌ D) {Y : D} {X : C}
    (f : Y ⟶ E.functor.obj X) :
    E.functor.map (E.inverse.map f ≫ E.unitIso.inv.app X) = E.counitIso.hom.app Y ≫ f := by
  rw [Functor.map_comp, ← E.counit_app_functor]
  exact E.counit_naturality f

/-- 同値による実現のfactor比較を送り直した自然変換の抽象的な計算。 -/
lemma equivalenceExtension_factor_whisker {B S : Type*} [Category* B] [Category* S]
    (L : B ⥤ S) (H : S ⥤ D) (F : B ⥤ C) (E : C ≌ D)
    (α : L ⋙ H ≅ F ⋙ E.functor) :
    Functor.whiskerRight
      ((Functor.associator L H E.inverse).symm ≪≫
        Functor.isoWhiskerRight α E.inverse ≪≫ Functor.associator F E.functor E.inverse ≪≫
        Functor.isoWhiskerLeft F E.unitIso.symm ≪≫ Functor.rightUnitor F).hom E.functor =
    (Functor.associator L (H ⋙ E.inverse) E.functor).hom ≫
      Functor.whiskerLeft L
        (Functor.associator H E.inverse E.functor ≪≫
          Functor.isoWhiskerLeft H E.counitIso ≪≫ Functor.rightUnitor H).hom ≫ α.hom := by
  apply NatTrans.ext
  funext X
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.leftUnitor_hom_app, Functor.rightUnitor_hom_app,
    Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.id_map,
    Category.id_comp, Category.comp_id] using
    (equivalence_map_inverse_then_unit E (α.hom.app X))

end SerrePositivity.DifferentialGraded
