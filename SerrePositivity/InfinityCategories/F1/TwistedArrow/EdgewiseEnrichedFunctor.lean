module

public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseEnrichedComparison

/-!
概要：豊穣関手を Hom の edgewise な共通解像の間の豊穣関手へ移す。
方針：各 Hom の射を重みからの射へ後合成し、同じ重みの点で単位・合成を比較する。
規約：元の豊穣圏に局所 Kan 性を要求しない。
使われ方：相対切断の図式の係数反転を全高次パラメーターで比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories

/-- 豊穣関手は Hom を edgewise 解像した豊穣圏の間の関手を誘導する。 -/
def edgewiseEnrichedFunctor {C : Type v} {D : Type w}
    [Category.{u} C] [SimplicialCategory C] [Category.{u} D] [SimplicialCategory D]
    (F : EnrichedFunctor SSet.{u} C D) :
    EnrichedFunctor SSet.{u} (EdgewiseEnrichedObject C) (EdgewiseEnrichedObject D) where
  obj X := ⟨F.obj X.val, trivial⟩
  map X Y := edgewiseSubdivisionMap (F.map X.val Y.val)
  map_id X := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    change (toUnit (edgewiseWeight.obj n.unop) ≫ eId SSet X.val) ≫ F.map X.val X.val = _
    rw [Category.assoc, F.map_id]
    rfl
  map_comp X Y Z := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨f, g⟩
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg (fun k : SimplicialCategory.sHom X.val Y.val ⊗
      SimplicialCategory.sHom Y.val Z.val ⟶ SimplicialCategory.sHom (F.obj X.val) (F.obj Z.val) ↦
        k.app d (f.app d x, g.app d x)) (F.map_comp X.val Y.val Z.val)

/-- 共通解像の右端射影は任意の豊穣関手と厳密に自然。 -/
lemma edgewiseEnrichedFunctor_right {C : Type v} {D : Type w}
    [Category.{u} C] [SimplicialCategory C] [Category.{u} D] [SimplicialCategory D]
    (F : EnrichedFunctor SSet.{u} C D) :
    (edgewiseEnrichedFunctor F).comp SSet (edgewiseEnrichedRight D) =
      (edgewiseEnrichedRight C).comp SSet F := by
  refine EnrichedFunctor.ext SSet (fun X ↦ rfl) ?_
  intro X Y
  simp only [eqToHom_refl, Category.comp_id]
  exact edgewiseRight_naturality (F.map X.val Y.val)

/-- 同じ厳密な自然性を coherent nerve の実際の射で回収する。 -/
lemma edgewiseEnrichedFunctor_infinity_right {C D : Type v}
    [Category.{u} C] [SimplicialCategory C] [Category.{u} D] [SimplicialCategory D]
    (F : EnrichedFunctor SSet.{u} C D) :
    coherentNerveMap (edgewiseEnrichedFunctor F) ≫ edgewiseEnrichedInfinityMap D =
      edgewiseEnrichedInfinityMap C ≫ coherentNerveMap F := by
  rw [edgewiseEnrichedInfinityMap, edgewiseEnrichedInfinityMap,
    ← coherentNerveMap_comp, edgewiseEnrichedFunctor_right, coherentNerveMap_comp]

end SerrePositivity.InfinityCategories
