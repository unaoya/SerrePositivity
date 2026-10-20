module

public import SerrePositivity.InfinityCategories.F1.EdgewiseOrdinaryLift
public import SerrePositivity.InfinityCategories.F1.EdgewiseOppositeKanEnriched

/-!
概要：strict な通常図式の共通 Hom 解像を、元の図式と元の反転図式に厳密に戻す。
方針：定値な Hom の左右の制限を計算し、豊穣関手の通常の作用の頂点表示を使う。
規約：共通解像上の一般の coherent な図式を strict な反転と同一視しない。
使われ方：同じ二脚の unstraightening 比較を、既存の strict な比較へ制限する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 定値な通常の射の右射影は、元の通常の射そのもの。 -/
lemma edgewiseOrdinaryLift_right (C : Type v) [Category.{u} C] [SimplicialCategory C] :
    edgewiseOrdinaryLift C ⋙ coherentEnrichedUnderlyingFunctor (edgewiseEnrichedRight C) = 𝟭 C := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  apply (SimplicialCategory.homEquiv' X Y).injective
  change SimplicialCategory.homEquiv' X Y
    ((coherentEnrichedUnderlyingFunctor (edgewiseEnrichedRight C)).map
      (edgewiseOrdinaryHom f)) = _
  refine (coherentEnrichedUnderlyingFunctor_vertex (edgewiseEnrichedRight C)
    (edgewiseOrdinaryHom f)).trans ?_
  rfl

/-- 定値な通常の Kan 射の左作用は、元の通常の射の単体集合としての反転そのもの。 -/
lemma edgewiseOrdinaryLift_opposite :
    edgewiseOrdinaryLift KanObject.{u} ⋙
      coherentEnrichedUnderlyingFunctor edgewiseOppositeKanEnriched = kanObjectOpFunctor := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  apply (SimplicialCategory.homEquiv'
    (kanObjectOpFunctor.obj X) (kanObjectOpFunctor.obj Y)).injective
  change SimplicialCategory.homEquiv' _ _
    ((coherentEnrichedUnderlyingFunctor edgewiseOppositeKanEnriched).map
      (edgewiseOrdinaryHom f)) = _
  refine (coherentEnrichedUnderlyingFunctor_vertex edgewiseOppositeKanEnriched
    (edgewiseOrdinaryHom f)).trans ?_
  apply CategoryTheory.Functor.functorHom_ext
  intro n α
  apply ConcreteCategory.hom_ext
  intro x
  rfl

end SerrePositivity.InfinityCategories
