module
public import SerrePositivity.KST.SConstruction.PointedMappingCylinderComponents
public import SerrePositivity.KST.SConstruction.PointedEnrichedMonicReplacement
public import SerrePositivity.KST.SConstruction.PointedEnrichedCylinderCompletion

/-! # 同じ厳密豊穣円柱置換の実点つき成分
概要：元の単射置換と実円柱押し出しの比較四角形は、基点固定の成分で元の射を回収する。
方針：同じ実円柱の辺から得た成分を、同じ Ex∞ 単位で後合成する。
規約：新たな局所化同値の反映は使わない。使われ方：実 BF 全帰納列の Ω 条件。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Limits SSet
open Spectra.PointedMapping
variable {C : Type v} [EnrichedCategory SSet.{u} C]

/-- 同じ Kan 単射置換は、元の射と標的比較の合成を点つき成分で回収する。 -/
lemma pointedEnrichedMonicReplacementSource_component
    (F G : EnrichedFunctor SSet.{u} C PointedSSetObject.{u})
    (t : ∀ X, F.obj X ⟶ G.obj X)
    (ht : ∀ X Y, F.map X Y ≫ eHomWhiskerLeft SSet (F.obj X) (t Y) =
      G.map X Y ≫ eHomWhiskerRight SSet (t X) (G.obj Y)) (X : C) :
    componentOf (show (F.obj X).obj ⟶
        ((pointedEnrichedMonicReplacementFunctor F G t ht).obj X).obj from
          pointedEnrichedMonicReplacementSource F G t ht X) =
      componentOf ((show (F.obj X).obj ⟶ (G.obj X).obj from t X) ≫
        (show (G.obj X).obj ⟶
          ((pointedEnrichedMonicReplacementFunctor F G t ht).obj X).obj from
            pointedEnrichedMonicReplacementTarget F G t ht X)) := by
  let f : (F.obj X).obj ⟶ (G.obj X).obj := t X
  let η : pointedTensorMappingCylinder f ⟶
      ((pointedEnrichedMonicReplacementFunctor F G t ht).obj X).obj :=
    pointedEnrichedMonicReplacementUnit F G t ht X
  have h := componentOf_comp_right (pointedTensorMappingCylinderSource_component f) η
  exact h.symm.trans (congrArg componentOf (Category.assoc _ _ _))

/-- 同じ実円柱 Kan 押し出しの両比較は、元の二脚と点つき成分で可換。 -/
lemma pointedEnrichedCylinderCompletion_component_square
    (F L R : EnrichedFunctor SSet.{u} C PointedSSetObject.{u})
    (l : ∀ X, F.obj X ⟶ L.obj X) (r : ∀ X, F.obj X ⟶ R.obj X)
    (hl : ∀ X Y, F.map X Y ≫ eHomWhiskerLeft SSet (F.obj X) (l Y) =
      L.map X Y ≫ eHomWhiskerRight SSet (l X) (L.obj Y))
    (hr : ∀ X Y, F.map X Y ≫ eHomWhiskerLeft SSet (F.obj X) (r Y) =
      R.map X Y ≫ eHomWhiskerRight SSet (r X) (R.obj Y)) (X : C) :
    componentOf ((show (F.obj X).obj ⟶ (L.obj X).obj from l X) ≫
        (show (L.obj X).obj ⟶
          ((pointedEnrichedCylinderCompletionFunctor F L R l r hl hr).obj X).obj from
            pointedEnrichedCylinderCompletionLeft F L R l r hl hr X)) =
      componentOf ((show (F.obj X).obj ⟶ (R.obj X).obj from r X) ≫
        (show (R.obj X).obj ⟶
          ((pointedEnrichedCylinderCompletionFunctor F L R l r hl hr).obj X).obj from
            pointedEnrichedCylinderCompletionRight F L R l r hl hr X)) := by
  let f : (F.obj X).obj ⟶ (L.obj X).obj := l X
  let g : (F.obj X).obj ⟶ (R.obj X).obj := r X
  let η : pushout (pointedTensorMappingCylinderSource f) g ⟶
      ((pointedEnrichedCylinderCompletionFunctor F L R l r hl hr).obj X).obj :=
    pointedEnrichedCylinderCompletionUnit F L R l r hl hr X
  have h := pointedDoubleMappingCylinder_component_square_post f g η
  change componentOf (f ≫ ((pointedTensorMappingCylinderTarget f ≫
    pushout.inl (pointedTensorMappingCylinderSource f) g) ≫ η)) =
      componentOf (g ≫ (pushout.inr (pointedTensorMappingCylinderSource f) g ≫ η))
  simpa only [Category.assoc] using h

end SerrePositivity.KST.SConstruction
