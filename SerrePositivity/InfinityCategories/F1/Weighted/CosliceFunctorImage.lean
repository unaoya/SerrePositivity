module

public import SerrePositivity.InfinityCategories.F1.Weighted.ConeFunctorImage
public import SerrePositivity.InfinityCategories.F1.Joins.CoslicePostCoordinates

/-!
概要：実際の weighted coslice 比較は豊穣関手による後合成と厳密に可換。
方針：始点の表示を正規化し、元の cone simplex の後合成の等式を全次数で使う。
規約：同値の逆の選択で比較を置き換えない。
使われ方：weighted nerve と反転係数の unstraightening の共同実現。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

variable {C D : Type v} [Category.{u} C] [Category.{u} D]
  [SimplicialCategory C] [SimplicialCategory D]

/-- 豊穣関手の coherent nerve は、始点の Yoneda 射を像の標準頂点の Yoneda 射へ写す。 -/
lemma coherentNerveMap_point_diagram (R : EnrichedFunctor SSet.{u} C D) (x : C) :
    SSet.yonedaEquiv.symm (coherentNerveVertex x) ≫ coherentNerveMap R =
      SSet.yonedaEquiv.symm (coherentNerveVertex (R.obj x)) := by
  rw [SSet.yonedaEquiv_symm_comp, coherentNerveMap_vertex]

/-- 元の coherent coslice の錐を豊穣関手で写し、同じ始点の標準表示へ正規化する。 -/
def coherentCosliceFunctorImage (R : EnrichedFunctor SSet.{u} C D) (x : C) :
    sliceUnder (SSet.yonedaEquiv.symm (coherentNerveVertex x)) ⟶
      sliceUnder (SSet.yonedaEquiv.symm (coherentNerveVertex (R.obj x))) :=
  sliceUnderPostcomp (SSet.yonedaEquiv.symm (coherentNerveVertex x)) (coherentNerveMap R) ≫
    eqToHom (congrArg sliceUnder (coherentNerveMap_point_diagram R x))

/-- 正規化した後合成は、元の錐の射そのものへの後合成。 -/
lemma coherentCosliceFunctorImage_app_val (R : EnrichedFunctor SSet.{u} C D) (x : C)
    {n : ℕ} (s : (sliceUnder (SSet.yonedaEquiv.symm (coherentNerveVertex x))) _⦋n⦌) :
    ((coherentCosliceFunctorImage R x).app (Opposite.op ⦋n⦌) s).val =
      s.val ≫ coherentNerveMap R := by
  change ((eqToHom (congrArg sliceUnder (coherentNerveMap_point_diagram R x))).app _
    ((sliceUnderPostcomp _ (coherentNerveMap R)).app _ s)).val = _
  rw [sliceUnder_eqToHom_app_val (coherentNerveMap_point_diagram R x)]
  rfl

/-- 同じ coslice の後合成は、底への射影を元の coherent nerve の射で被覆する。 -/
lemma coherentCosliceFunctorImage_projection (R : EnrichedFunctor SSet.{u} C D) (x : C) :
    coherentCosliceFunctorImage R x ≫
      sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex (R.obj x))) =
    sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)) ≫
      coherentNerveMap R := by
  rw [coherentCosliceFunctorImage, Category.assoc,
    sliceUnder_eqToHom_projection (coherentNerveMap_point_diagram R x)]
  exact sliceUnderPostcomp_projection _ _

/-- 元の全 weighted coslice 比較は、全係数単体で豊穣関手の後合成と厳密に可換。 -/
lemma weightedCosliceComparison_functorImage {I : Type u} [SmallCategory I]
    (F : I ⥤ C) (R : EnrichedFunctor SSet.{u} C D) (x : C) :
    weightedCosliceComparison F x ≫ coherentCosliceFunctorImage R x =
      (SSet.uliftFunctor.{v, u}).map
        (weightedNerveMap (Functor.whiskerRight (weightedHomFunctorImage F R x) SSet.opFunctor)) ≫
        weightedCosliceComparison (F ⋙ coherentEnrichedUnderlyingFunctor R) (R.obj x) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  change ((coherentCosliceFunctorImage R x).app (Opposite.op ⦋n⦌)
    ((weightedCosliceComparison F x).app _ s)).val = _
  rw [coherentCosliceFunctorImage_app_val]
  change ((leftPointStdSimplexIso n).hom ≫
    SSet.yonedaEquiv.symm (weightedConeSimplex F x s.down.2)) ≫ coherentNerveMap R = _
  rw [Category.assoc, SSet.yonedaEquiv_symm_comp]
  change (leftPointStdSimplexIso n).hom ≫
    SSet.yonedaEquiv.symm (show (SimplicialNerve D) _⦋n + 1⦌ from
      (weightedConeSimplex F x s.down.2).comp SSet R) = _
  rw [weightedConeSimplex_functorImage]
  rfl

end SerrePositivity.InfinityCategories
