module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftRows
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionFrameRowFunctor
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionCenters

/-! # Full row lifts from the same actual changing-center fiber diagram -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionCenterRowLifts
variable (C : Type u) [Category.{v} C] [ModelCategory C]
local instance : ModelCategory (SimplexCategory ⥤ C) := Reedy.simplexModelCategory C

def map (q : ResolutionArrowDiagram.Index C) {T : SSet.{v}}
    (s : T ⟶ (ResolutionArrowDiagram.fibers C).obj q) (n : SimplexCategoryᵒᵖ) (x : T.obj n) :
    ResolutionFrameRows.row (ResolutionArrowDiagram.source C q).inner n.unop ⟶
      ResolutionArrowDiagram.target C q :=
  ResolutionLiftRows.map _ _ _ (s ≫ (ResolutionArrowDiagram.fiberIso C q).hom) n x

lemma diagram (q : ResolutionArrowDiagram.Index C) {T : SSet.{v}}
    (s : T ⟶ (ResolutionArrowDiagram.fibers C).obj q) (n : SimplexCategoryᵒᵖ) (x : T.obj n) :
    (map C q s n x).diagram =
      ((s ≫ (FiberFunctor.inclusion (ResolutionArrowDiagram.rawProjection C)
        (ResolutionArrowDiagram.basepoint C)).app q).app n x) := by
  change (((s ≫ (ResolutionArrowDiagram.fiberIso C q).hom) ≫
    ResolutionLiftSpace.inclusion _ _ _).app n x) = _
  rw [Category.assoc, ResolutionArrowDiagram.fiberIso_inclusion]
  rfl

lemma naturality (q : ResolutionArrowDiagram.Index C) {T : SSet.{v}}
    (s : T ⟶ (ResolutionArrowDiagram.fibers C).obj q)
    {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (x : T.obj n) :
    ResolutionFrameRows.rowMap (ResolutionArrowDiagram.source C q).inner θ.unop ≫
        map C q s n x = map C q s m (T.map θ x) :=
  ResolutionLiftRows.naturality _ _ _ _ θ x

lemma transport {q r : ResolutionArrowDiagram.Index C} (k : q ⟶ r) {T : SSet.{v}}
    (s : T ⟶ (ResolutionArrowDiagram.fibers C).obj q) (n : SimplexCategoryᵒᵖ) (x : T.obj n) :
    map C r (s ≫ (ResolutionArrowDiagram.fibers C).map k) n x =
      (ResolutionFrameRowFunctor.component k.hom.1.unop n.unop ≫ map C q s n x) ≫ k.hom.2 := by
  apply ResolutionObject.Hom.ext
  · exact (ResolutionArrowDiagram.equation C k).symm
  · change (map C r (s ≫ (ResolutionArrowDiagram.fibers C).map k) n x).diagram =
      (k.hom.1.unop.frame.app n.unop ≫ (map C q s n x).diagram) ≫ k.hom.2.diagram
    rw [diagram, diagram]
    have h := congrArg (fun f => f.app n x)
      ((Category.assoc s ((ResolutionArrowDiagram.fibers C).map k) _).trans
        (congrArg (fun f => s ≫ f) (ResolutionArrowDiagram.map_inclusion C k)))
    exact h

end SerrePositivity.HomotopyFunctionComplex.ResolutionCenterRowLifts
