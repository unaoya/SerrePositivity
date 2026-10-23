module

public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseEnrichedFunctor
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseOppositeKanComparison
public import SerrePositivity.InfinityCategories.F1.KanModels.KanEnrichedDiagramComparison

/-!
概要：Kan 値豊穣関手の係数の共通解像と反転を、豊穣な比較にも適用する。
方針：元の Hom を edgewise 解像し、同じ重みの各点で比較の全高次の自然性を使う。
規約：通常の係数反転を元の Hom 上で豊穣関手と仮定しない。
使われ方：strict transport と相対表現の係数比較を全対象で共同実現する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories

/-- Kan 値豊穣関手の係数と Hom パラメーターを同時に共通解像へ移す。 -/
def kanEnrichedFunctorEdgewise {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (F : EnrichedFunctor SSet.{u} C KanObject.{u}) :
    EnrichedFunctor SSet.{u} (EdgewiseEnrichedObject C) KanObject.{u} :=
  (edgewiseEnrichedFunctor F).comp SSet edgewiseKanEnriched

/-- 共通解像した Hom 上で、Kan 値豊穣関手の係数を反転する。 -/
def kanEnrichedFunctorOpposite {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (F : EnrichedFunctor SSet.{u} C KanObject.{u}) :
    EnrichedFunctor SSet.{u} (EdgewiseEnrichedObject C) KanObject.{u} :=
  (edgewiseEnrichedFunctor F).comp SSet edgewiseOppositeKanEnriched

/-- 豊穣自然な比較の共通解像は、解像した Hom の全パラメーターに関して自然。 -/
def KanEnrichedComparison.edgewise {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {F G : EnrichedFunctor SSet.{u} C KanObject.{u}} (η : KanEnrichedComparison F G) :
    KanEnrichedComparison (kanEnrichedFunctorEdgewise F) (kanEnrichedFunctorEdgewise G) := by
  refine ⟨fun X ↦ edgewiseSubdivisionMap (η.val X.val), ?_⟩
  intro X Y
  change (edgewiseSubdivisionMap (η.val X.val) ▷
    edgewiseSubdivision (SimplicialCategory.sHom X.val Y.val)) ≫
      uncurry (edgewiseSubdivisionMap (G.map X.val Y.val) ≫
        edgewiseKanEnrichedMap (G.obj X.val).obj (G.obj Y.val).obj) =
    uncurry (edgewiseSubdivisionMap (F.map X.val Y.val) ≫
      edgewiseKanEnrichedMap (F.obj X.val).obj (F.obj Y.val).obj) ≫
        edgewiseSubdivisionMap (η.val Y.val)
  rw [uncurry_natural_left, uncurry_natural_left, edgewiseKanEnrichedMap,
    edgewiseKanEnrichedMap, uncurry_curry, uncurry_curry]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨x, f⟩
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  exact kanEnrichedComparison_app η X.val Y.val (f.app d s) (𝟙 d) (x.app d s)

/-- 豊穣自然な比較は、Hom を解像した上で係数を反転しても豊穣自然。 -/
def KanEnrichedComparison.opposite {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {F G : EnrichedFunctor SSet.{u} C KanObject.{u}} (η : KanEnrichedComparison F G) :
    KanEnrichedComparison (kanEnrichedFunctorOpposite F) (kanEnrichedFunctorOpposite G) := by
  refine ⟨fun X ↦ SSet.opFunctor.map (η.val X.val), ?_⟩
  intro X Y
  change (SSet.opFunctor.map (η.val X.val) ▷
    edgewiseSubdivision (SimplicialCategory.sHom X.val Y.val)) ≫
      uncurry (edgewiseSubdivisionMap (G.map X.val Y.val) ≫
        edgewiseOppositeKanEnrichedMap (G.obj X.val).obj (G.obj Y.val).obj) =
    uncurry (edgewiseSubdivisionMap (F.map X.val Y.val) ≫
      edgewiseOppositeKanEnrichedMap (F.obj X.val).obj (F.obj Y.val).obj) ≫
        SSet.opFunctor.map (η.val Y.val)
  rw [uncurry_natural_left, uncurry_natural_left, edgewiseOppositeKanEnrichedMap,
    edgewiseOppositeKanEnrichedMap, uncurry_curry, uncurry_curry]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨x, f⟩
  exact kanEnrichedComparison_app η X.val Y.val
    ((edgewiseLeft (SimplicialCategory.sHom X.val Y.val)).app n f) (𝟙 n) x

end SerrePositivity.InfinityCategories
