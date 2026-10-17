module
public import SerrePositivity.DifferentialGraded.Bimodule.PairedRestriction
public import SerrePositivity.DifferentialGraded.Bimodule.MiddleLeftRestrictionCoherence
public import SerrePositivity.DifferentialGraded.Bimodule.MiddleRightRestrictionCoherence

/-! # 直接の両端制限の恒等・合成比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t s r
namespace SerrePositivity.DifferentialGraded.BimoduleCategory
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C]

/-- 恒等の両端制限を、既存の左右の恒等比較で元に戻す。 -/
def pairedRestrictionIdObjIso (P : BimoduleCategory A B C) :
    (pairedRestrictionFunctor A B C B C (DGFunctor.id B) (DGFunctor.id C)).obj P ≅ P :=
  (middleRightRestrictionFunctor A B B C (DGFunctor.id B)).mapIso
      (middleLeftRestrictionIdObjIso A B C P) ≪≫
    middleRightRestrictionIdObjIso A B C P

@[simp]
lemma pairedRestrictionIdObjIso_hom_value (P : BimoduleCategory A B C) (b : B) (c : C) :
    (valueEvaluation A B C b c).map (pairedRestrictionIdObjIso A B C P).hom = 𝟙 _ := by
  simp only [pairedRestrictionIdObjIso, Iso.trans_hom, Functor.mapIso_hom,
    CategoryTheory.Functor.map_comp]
  have h := middleRightRestrictionMap_value_eval A B B C (DGFunctor.id B)
    (middleLeftRestrictionIdObjIso A B C P).hom b c
  change (valueEvaluation A B C b c).map
    (middleRightRestrictionMap A B B C (DGFunctor.id B)
      (middleLeftRestrictionIdObjIso A B C P).hom) ≫ _ = _
  rw [h, middleRightRestrictionIdObjIso_hom_value]
  change (moduleEvaluation A B b).map
      ((evaluation A B C c).map (middleLeftRestrictionIdObjIso A B C P).hom) ≫ 𝟙 _ = _
  rw [middleLeftRestrictionIdObjIso_hom_eval, CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

def pairedRestrictionIdIso :
    pairedRestrictionFunctor A B C B C (DGFunctor.id B) (DGFunctor.id C) ≅
      𝟭 (BimoduleCategory A B C) :=
  NatIso.ofComponents (pairedRestrictionIdObjIso A B C) (by
    intro P Q q
    change (pairedRestrictionFunctor A B C B C (DGFunctor.id B) (DGFunctor.id C)).map q ≫
      (pairedRestrictionIdObjIso A B C Q).hom = (pairedRestrictionIdObjIso A B C P).hom ≫ q
    apply value_hom_ext A B C
    intro b c
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    rw [pairedRestrictionIdObjIso_hom_value A B C Q b c,
      pairedRestrictionIdObjIso_hom_value A B C P b c, pairedRestrictionFunctor_map_value]
    change (valueEvaluation A B C b c).map q ≫ 𝟙 _ =
      𝟙 _ ≫ (valueEvaluation A B C b c).map q
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

variable (E : Type z) [DGCategory A E] [Small.{u} E]
  (L : Type t) [DGCategory A L] (D : Type s) [DGCategory A D] [Small.{u} D]
  (K : Type r) [DGCategory A K] (F : DGFunctor A D E) (G : DGFunctor A E B)
  (H : DGFunctor A K L) (I : DGFunctor A L C)

/-- 二段階の両端制限を合成関手による制限へ送る。左右の交換比較を明示する。 -/
def pairedRestrictionCompObjIso (P : BimoduleCategory A B C) :
    (pairedRestrictionFunctor A E L D K F H).obj
        ((pairedRestrictionFunctor A B C E L G I).obj P) ≅
      (pairedRestrictionFunctor A B C D K (F.comp G) (H.comp I)).obj P :=
  (middleRightRestrictionFunctor A E D K F).mapIso
      (pairedRestrictionInterchangeObjIso A B L E K G H
        ((middleLeftRestrictionFunctor A B C L I).obj P)).symm ≪≫
    middleRightRestrictionCompObjIso A D K E B F G
      ((middleLeftRestrictionFunctor A B L K H).obj
        ((middleLeftRestrictionFunctor A B C L I).obj P)) ≪≫
    (middleRightRestrictionFunctor A B D K (F.comp G)).mapIso
      (middleLeftRestrictionCompObjIso A B K L C H I P)

@[simp]
lemma pairedRestrictionCompObjIso_hom_value (P : BimoduleCategory A B C) (d : D) (k : K) :
    (valueEvaluation A D K d k).map
        (pairedRestrictionCompObjIso A B C E L D K F G H I P).hom = 𝟙 _ := by
  have h₁ := middleRightRestrictionMap_value_eval A E D K F
    (pairedRestrictionInterchangeObjIso A B L E K G H
      ((middleLeftRestrictionFunctor A B C L I).obj P)).inv d k
  have h₃ := middleRightRestrictionMap_value_eval A B D K (F.comp G)
    (middleLeftRestrictionCompObjIso A B K L C H I P).hom d k
  have hv : (evaluation A E K k).map
      (pairedRestrictionInterchangeObjIso A B L E K G H
        ((middleLeftRestrictionFunctor A B C L I).obj P)).inv = 𝟙 _ := by
    simp only [pairedRestrictionInterchangeObjIso, eqToIso.inv, eqToHom_map]
    rfl
  have h₁' : (valueEvaluation A E K (F.obj d) k).map
      (pairedRestrictionInterchangeObjIso A B L E K G H
        ((middleLeftRestrictionFunctor A B C L I).obj P)).inv = 𝟙 _ := by
    change (moduleEvaluation A E (F.obj d)).map
      ((evaluation A E K k).map
        (pairedRestrictionInterchangeObjIso A B L E K G H
          ((middleLeftRestrictionFunctor A B C L I).obj P)).inv) = _
    rw [hv, CategoryTheory.Functor.map_id]
    rfl
  have h₃' : (valueEvaluation A B K ((F.comp G).obj d) k).map
      (middleLeftRestrictionCompObjIso A B K L C H I P).hom = 𝟙 _ := by
    change (moduleEvaluation A B (G.obj (F.obj d))).map
      ((evaluation A B K k).map (middleLeftRestrictionCompObjIso A B K L C H I P).hom) = _
    rw [middleLeftRestrictionCompObjIso_hom_eval, CategoryTheory.Functor.map_id]
    rfl
  simp only [pairedRestrictionCompObjIso, Iso.trans_hom, Functor.mapIso_hom,
    CategoryTheory.Functor.map_comp]
  change (valueEvaluation A D K d k).map (middleRightRestrictionMap A E D K F
      (pairedRestrictionInterchangeObjIso A B L E K G H
        ((middleLeftRestrictionFunctor A B C L I).obj P)).inv) ≫
    (valueEvaluation A D K d k).map (middleRightRestrictionCompObjIso A D K E B F G
      ((middleLeftRestrictionFunctor A B L K H).obj
        ((middleLeftRestrictionFunctor A B C L I).obj P))).hom ≫
    (valueEvaluation A D K d k).map (middleRightRestrictionMap A B D K (F.comp G)
      (middleLeftRestrictionCompObjIso A B K L C H I P).hom) = _
  rw [h₁, h₃, h₁', h₃', middleRightRestrictionCompObjIso_hom_value]
  change (𝟙 ((underlying A B C P).value (G.obj (F.obj d)) (I.obj (H.obj k)))) ≫
    𝟙 _ ≫ 𝟙 _ = 𝟙 _
  rw [Category.id_comp, Category.id_comp]

def pairedRestrictionCompIso :
    pairedRestrictionFunctor A B C E L G I ⋙ pairedRestrictionFunctor A E L D K F H ≅
      pairedRestrictionFunctor A B C D K (F.comp G) (H.comp I) :=
  NatIso.ofComponents (pairedRestrictionCompObjIso A B C E L D K F G H I) (by
    intro P Q q
    change ((pairedRestrictionFunctor A B C E L G I ⋙
      pairedRestrictionFunctor A E L D K F H).map q) ≫
      (pairedRestrictionCompObjIso A B C E L D K F G H I Q).hom =
      (pairedRestrictionCompObjIso A B C E L D K F G H I P).hom ≫
      (pairedRestrictionFunctor A B C D K (F.comp G) (H.comp I)).map q
    apply value_hom_ext A D K
    intro d k
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    rw [pairedRestrictionCompObjIso_hom_value A B C E L D K F G H I Q d k,
      pairedRestrictionCompObjIso_hom_value A B C E L D K F G H I P d k]
    simp only [Functor.comp_map, pairedRestrictionFunctor_map_value]
    change (valueEvaluation A B C (G.obj (F.obj d)) (I.obj (H.obj k))).map q ≫ 𝟙 _ =
      𝟙 _ ≫ (valueEvaluation A B C (G.obj (F.obj d)) (I.obj (H.obj k))).map q
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

end SerrePositivity.DifferentialGraded.BimoduleCategory
