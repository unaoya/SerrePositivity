module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeNormalizationOriginalFace
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeHomModelCancellation
public import SerrePositivity.InfinityCategories.Derived.Gluing.ArrowHomActionPrism
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomArrowInterval

/-! 正本の矢印 Hom の全四角形は、元 pinched Hom 上の同じ native cube 面そのもの。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory MonoidalClosed DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)

def dgGluingNativeHomModelMap :=
  (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
    (pinchedComplexModelIso (A := R) X Y).hom

lemma dgGluingNativeArrowComparisonPrism :
    intervalFunctorHomPrism (dgGluingNativeHomModelMap R C D M X Y ≫
      dgGluingLaxHomArrowIntervalComparison R C D M X Y) =
      ((β_ (Δ[1] : SSet.{max (u + 1) v w}) Δ[1]).hom ▷
        (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
          (DGNerve.pinchedHom R (DGGluingObject R C D M) X Y)) ≫
        (α_ Δ[1] Δ[1] _).hom ≫
          (Δ[1] ◁ dgGluingNativeHomIntervalEvaluation R C D M X Y) ≫
            (β_ (Δ[1] : SSet.{max (u + 1) v w})
              ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
                (dgNerve R (DGGluingObject R C D M)))).hom ≫
                  (dgGluingUniverseDerivedAugmentationHomotopy R C D M).h := by
  rw [dgGluingLaxHomArrowIntervalComparison_action, dgGluingNativeHomModelMap,
    ← Category.assoc, dgGluingNativeHomModelCancellation]
  rw [dgGluingArrowHomActionPrism (dgGluingUniverseDerivedAugmentationArrowFamily R C D M)
    (dgGluingDerivedAugmentationArrowDiagram_vertex R C D M X)
    (dgGluingDerivedAugmentationArrowDiagram_vertex R C D M Y)]
  rw [← dgGluingUliftPinchedInterval_uncurry R (DGGluingObject R C D M) X Y]
  rw [dgGluingUniverseDerivedAugmentationArrowFamily, uncurry_curry]
  rfl

end SerrePositivity.InfinityCategories
