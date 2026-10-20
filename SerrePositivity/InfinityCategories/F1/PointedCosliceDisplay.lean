module

public import SerrePositivity.InfinityCategories.F1.StrictKanUnstraighteningComparison

/-!
概要：標準一点の coherent 頂点で表示した coslice を、実際の pointed space 表示へ戻す。
方針：頂点の厳密な等式で移送し、pullback の第一射影との可換性を証明する。
規約：元の unstraightening 比較と pointed 射影をそのまま保持する。
使われ方：全 coslice prism を実際の native pointed prism へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

private lemma cosliceVertexDisplay_projection {X : SSet.{u}} {x y : X _⦋0⦌} (h : x = y) :
    eqToHom (congrArg (fun v => sliceUnder (SSet.yonedaEquiv.symm v)) h) ≫
      sliceUnderProjection (SSet.yonedaEquiv.symm y) =
    sliceUnderProjection (SSet.yonedaEquiv.symm x) := by
  subst y
  simp

private lemma coneTotalDisplay_fst {K X : SSet.{u}} {F G : K ⟶ X}
    {x y : X _⦋0⦌} (hF : F = G) (hx : x = y) :
    eqToHom (congrArg₂ coherentConeTotal hF hx) ≫
        pullback.fst (sliceUnderProjection (SSet.yonedaEquiv.symm y)) G =
    pullback.fst (sliceUnderProjection (SSet.yonedaEquiv.symm x)) F ≫
      eqToHom (congrArg (fun v => sliceUnder (SSet.yonedaEquiv.symm v)) hx) := by
  subst G
  subst y
  simp

/-- coherent 頂点で表示した標準一点の coslice を、元の pointed space の表示へ移す。 -/
def pointedCosliceDisplay :
    sliceUnder (SSet.yonedaEquiv.symm (coherentNerveVertex pointKanObject.{u})) ⟶
      PointedSpaceInfinity.{u} :=
  eqToHom (congrArg (fun v => sliceUnder (SSet.yonedaEquiv.symm v))
    (spaceInfinityVertex_eq_coherent pointKanObject.{u}).symm)

/-- 一点の表示変更は、元の pointed space の射影と厳密に可換。 -/
lemma pointedCosliceDisplay_projection :
    pointedCosliceDisplay.{u} ≫ pointedSpaceProjection =
      sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex pointKanObject.{u})) := by
  exact cosliceVertexDisplay_projection (spaceInfinityVertex_eq_coherent pointKanObject.{u}).symm

/-- strict な全空間の表示変更の第一射影は、同じ一点 coslice の表示変更そのもの。 -/
lemma strictKanUnstraighteningIso_pointed {I : Type u} [SmallCategory I]
    (F : I ⥤ KanObject.{u}) :
    (strictKanUnstraighteningIso F).hom ≫
      pullback.fst pointedSpaceProjection (kanDiagramCoherentNerve F) =
    pullback.fst
      (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex pointKanObject.{u})))
      (strictCoherentDiagram F) ≫ pointedCosliceDisplay := by
  exact coneTotalDisplay_fst (kanDiagramCoherentNerve_eq_strictCoherentDiagram F).symm
    (spaceInfinityVertex_eq_coherent pointKanObject.{u}).symm

/-- 元の weighted coslice 比較を一点の表示で戻すと、元の unstraightening 比較の第一射影。 -/
lemma weightedCosliceComparison_pointed {I : Type u} [SmallCategory I]
    (F : I ⥤ KanObject.{u}) :
    weightedCosliceComparison F pointKanObject ≫ pointedCosliceDisplay =
    strictKanUnstraighteningComparison F ≫
      pullback.fst pointedSpaceProjection (kanDiagramCoherentNerve F) := by
  rw [strictKanUnstraighteningComparison, Category.assoc,
    strictKanUnstraighteningIso_pointed, ← Category.assoc]
  change _ = (pullback.lift (weightedCosliceComparison F pointKanObject) _ _ ≫
    pullback.fst _ _) ≫ pointedCosliceDisplay
  rw [pullback.lift_fst]

end SerrePositivity.InfinityCategories
