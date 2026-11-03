module

public import SerrePositivity.InfinityCategories.Core.Opposite
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Categories.PointedSpaces
public import SerrePositivity.InfinityCategories.F1.Fibrations.FiberComparisonBaseChange
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningInfinityReconstruction
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningRepresentation
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallLeftUnstraightening
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallLeftUnstraighteningBaseChange
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseEndpoints
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseSubdivision
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.LeftFibration
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.PointedDisplay
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.PointedIdentity
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.Projection
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.TwistedElementsBaseChange
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.TwistedElementsReconstruction
public import SerrePositivity.InfinityCategories.F1.Yoneda.YonedaInfinityConstruction
public import SerrePositivity.InfinityCategories.F1B.Fibrations.InnerProductProjection

/-!
概要：元の共同 Hom の復元射の pointed 成分を、同じ Tw 全体の復元へ戻す。
方針：同じ底変換の同型の第一射影と、縮小した pointed 成分の自然性を使う。
規約：全ての終点パラメータを保つ厳密な等式。
使われ方：元の恒等点復元射の始値と c1 の canonical な恒等点との一致。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {E C : SSet.{u}} [Quasicategory C] (p : E ⟶ C)
local notation "H" => twistedElementsHomDiagram p
local notation "T" => twistedArrowHomInfinity C
local instance : Quasicategory (C.op ⊗ C) :=
  quasicategory_of_innerFibration (fst C.op C)

/-- 同じ復元射を Tw の全 unstraightening へ戻すと、元の全体の復元そのもの。 -/
lemma twistedElementsReconstruction_globalMap :
    twistedElementsReconstruction p ≫
      smallLeftUnstraighteningMap H T (twistedElementsBaseMap p) rfl =
    pullback.fst (edgewiseRight C) p ≫
      leftStraighteningInfinityReconstruction (twistedArrowProjection C) := by
  rw [twistedElementsReconstruction, Category.assoc, Category.assoc,
    show (twistedElementsUnstraighteningIso p).inv ≫
      smallLeftUnstraighteningMap H T (twistedElementsBaseMap p) rfl = _ from
        (smallLeftUnstraighteningMap_isPullback H T
          (twistedElementsBaseMap p) rfl).isoPullback_inv_fst,
    fiberComparisonBaseChange, pullback.lift_fst, ← Category.assoc]
  simp only [twistedElementsBaseChangeIso, twistedElementsToBaseChange, pullback.lift_fst]

/-- 同じ復元射の pointed 成分は、元の Tw 全体の pointed 表示の同じ制限。 -/
lemma twistedElementsReconstruction_pointed :
    (SSet.uliftFunctor.{u + 1, u}).map (twistedElementsReconstruction p) ≫
      smallLeftUnstraighteningPointedMap H =
    (SSet.uliftFunctor.{u + 1, u}).map (pullback.fst (edgewiseRight C) p) ≫
      twistedArrowPointedDisplay C := by
  rw [← smallLeftUnstraighteningPointedMap_naturality H T (twistedElementsBaseMap p) rfl,
    ← Category.assoc, ← Functor.map_comp, twistedElementsReconstruction_globalMap,
    Functor.map_comp, Category.assoc]
  rfl

end SerrePositivity.InfinityCategories.F2.Ind
