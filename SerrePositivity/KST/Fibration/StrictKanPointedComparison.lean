module
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.StrictKanUnstraighteningComparison

/-! # strict Kan 比較の pointed 射影を、同じ coherent 錐の第一射影で計算する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 錐図式と頂点の等号による移送は、元の第一射影も同じ等号で移送する。 -/
theorem coherentConeTotal_transport_fst {K X : SSet.{u}} {F G : K ⟶ X}
    {x y : X _⦋0⦌} (hF : F = G) (hx : x = y)
    (h : HomotopyLimits.coherentConeTotal F x = HomotopyLimits.coherentConeTotal G y) :
    eqToHom h ≫ pullback.fst (sliceUnderProjection (SSet.yonedaEquiv.symm y)) G =
      pullback.fst (sliceUnderProjection (SSet.yonedaEquiv.symm x)) F ≫
        eqToHom (congrArg (fun z => sliceUnder (SSet.yonedaEquiv.symm z)) hx) := by
  subst G
  subst y
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- coherent な一点から空間圏の一点への同じ頂点等号による coslice の移送。 -/
def strictKanPointedApexIso :
    sliceUnder (SSet.yonedaEquiv.symm (coherentNerveVertex pointKanObject.{u})) ≅
      PointedSpaceInfinity.{u} :=
  eqToIso (congrArg (fun z => sliceUnder (SSet.yonedaEquiv.symm z))
    (spaceInfinityVertex_eq_coherent pointKanObject.{u}).symm)

/-- strict Kan の全空間同型は、元の第一射影を同じ apex 移送で保つ。 -/
theorem strictKanUnstraighteningIso_fst {I : Type u} [Category.{u} I]
    (F : I ⥤ KanObject.{u}) :
    (strictKanUnstraighteningIso F).hom ≫
      pullback.fst pointedSpaceProjection (kanDiagramCoherentNerve F) =
    pullback.fst
      (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex pointKanObject)))
      (HomotopyLimits.strictCoherentDiagram F) ≫ strictKanPointedApexIso.hom := by
  let hd := (kanDiagramCoherentNerve_eq_strictCoherentDiagram F).symm
  let hx := (spaceInfinityVertex_eq_coherent pointKanObject).symm
  exact coherentConeTotal_transport_fst hd hx (congrArg₂ HomotopyLimits.coherentConeTotal hd hx)

/-- 同じ strict Kan 実比較の pointed map は、元の weighted coslice 比較そのもの。 -/
theorem strictKanUnstraighteningComparison_pointed {I : Type u} [Category.{u} I]
    (F : I ⥤ KanObject.{u}) :
    strictKanUnstraighteningComparison F ≫
      pullback.fst pointedSpaceProjection (kanDiagramCoherentNerve F) =
    HomotopyLimits.weightedCosliceComparison F pointKanObject ≫
      strictKanPointedApexIso.hom := by
  rw [strictKanUnstraighteningComparison, Category.assoc, strictKanUnstraighteningIso_fst,
    ← Category.assoc]
  rw [HomotopyLimits.weightedCoherentConeComparison, pullback.lift_fst]

end SerrePositivity.KST.Fibration
