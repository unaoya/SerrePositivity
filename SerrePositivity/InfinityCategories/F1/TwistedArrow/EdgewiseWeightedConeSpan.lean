module

public import SerrePositivity.InfinityCategories.F1.Weighted.ConeFunctorEquivalence
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseOppositeHomEquivalence
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseEnrichedComparison

/-!
概要：Hom の共通解像の同じ weighted cone 全空間から、直値と反転値の全空間へ比較する。
方針：二つの実際の豊穣関手の Hom の同値を、元の cone 比較の可換式へ適用する。
規約：二つの標的や係数を同一視せず、同じ始域からの二脚として保持する。
使われ方：weighted nerve と反転係数の unstraightening の共同比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

local instance : ∀ X Y : EdgewiseEnrichedObject KanObject.{u},
    KanComplex (SimplicialCategory.sHom X Y) := fun X Y =>
  inferInstanceAs (KanComplex (edgewiseSubdivision (SimplicialCategory.sHom X.val Y.val)))

local instance {I : Type u} [SmallCategory I] {C : Type (u + 1)} [Category.{u} C]
    [SimplicialCategory C] [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    (F : I ⥤ C) (x : C) :
    Quasicategory (coherentConeTotal (strictCoherentDiagram F) (coherentNerveVertex x)) :=
  quasicategory_of_innerFibration
    (coherentConeProjection (strictCoherentDiagram F) (coherentNerveVertex x))

/-- 共通 Hom 解像の cone 全空間から直値側への実際の右射影は、全空間の前合成同値。 -/
lemma edgewiseCoherentConeRight_isPrecompositionEquivalence
    {I : Type u} [SmallCategory I] (F : I ⥤ EdgewiseEnrichedObject KanObject.{u})
    (x : EdgewiseEnrichedObject KanObject.{u}) :
    IsPrecompositionEquivalence
      (coherentConeTotalFunctorImage F (edgewiseEnrichedRight KanObject.{u}) x) := by
  apply coherentConeTotalFunctorImage_isPrecompositionEquivalence
  intro i
  exact isQCatEquivalence_of_trivialKanFibration
    (edgewiseRight (SimplicialCategory.sHom x.val (F.obj i).val))

/-- 同じ共通 Hom 解像から反転値側への実際の左作用も、全空間の前合成同値。 -/
lemma edgewiseCoherentConeOpposite_isPrecompositionEquivalence
    {I : Type u} [SmallCategory I] (F : I ⥤ EdgewiseEnrichedObject KanObject.{u})
    (x : EdgewiseEnrichedObject KanObject.{u}) :
    IsPrecompositionEquivalence
      (coherentConeTotalFunctorImage F edgewiseOppositeKanEnriched x) := by
  apply coherentConeTotalFunctorImage_isPrecompositionEquivalence
  intro i
  exact edgewiseOppositeKanEnrichedMap_isQCatEquivalence x.val.obj (F.obj i).val.obj

/-- 右脚そのものの全空間の同値性は、後の比較の逆を同じ右脚に固定できる。 -/
lemma edgewiseCoherentConeRight_isQCatEquivalence
    {I : Type u} [SmallCategory I] (F : I ⥤ EdgewiseEnrichedObject KanObject.{u})
    (x : EdgewiseEnrichedObject KanObject.{u}) :
    IsQCatEquivalence
      (coherentConeTotalFunctorImage F (edgewiseEnrichedRight KanObject.{u}) x) :=
  (edgewiseCoherentConeRight_isPrecompositionEquivalence F x).isQCatEquivalence

/-- 左脚そのものの全空間の同値性は、元の反転 Hom の作用を順方向に保持する。 -/
lemma edgewiseCoherentConeOpposite_isQCatEquivalence
    {I : Type u} [SmallCategory I] (F : I ⥤ EdgewiseEnrichedObject KanObject.{u})
    (x : EdgewiseEnrichedObject KanObject.{u}) :
    IsQCatEquivalence (coherentConeTotalFunctorImage F edgewiseOppositeKanEnriched x) :=
  (edgewiseCoherentConeOpposite_isPrecompositionEquivalence F x).isQCatEquivalence

end SerrePositivity.InfinityCategories
