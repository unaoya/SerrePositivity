module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixedTransport

/-! # Exact external postcomposition of the prescribed factorization points

The interpolation before a cut is unchanged, and the remaining actual
postcomposition maps associate strictly after their explicit base casts.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.SimplicialModel
open SerrePositivity.HomotopyFunctionComplex.CoherentLiftRelative

namespace SerrePositivity.HomotopyFunctionComplex.AllFactorizationPostPoints
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
local instance : ModelCategory (SimplexCategory ⥤ C) := Reedy.simplexModelCategory C

variable {X Y M V W : ResolutionObject C} (f : X.base ⟶ Y.base)
  (l : Y ⟶ M) (r : M ⟶ V) (g : Y ⟶ V) (e : l ≫ r = g)

abbrev tailTo : ResolutionLiftSpace.obj X M (f ≫ l.base) ⟶
    ResolutionLiftSpace.obj X V (f ≫ g.base) :=
  CoherentLiftPostComposition.tailMap X Y M V f l r ≫
    ResolutionLiftSpace.baseChange (congrArg (fun k => f ≫ k.base) e)

omit [ModelCategory SSet.{v}] in
lemma tailTo_inclusion : tailTo f l r g e ≫ ResolutionLiftSpace.inclusion X V (f ≫ g.base) =
    ResolutionLiftSpace.inclusion X M (f ≫ l.base) ≫
      (cosimplicialHom (ResolutionLiftSpace.frame X).obj).map r.diagram := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun q => CoherentLiftPostComposition.tailMap X Y M V f l r ≫ q)
      (ResolutionLiftSpace.baseChange_inclusion (congrArg (fun k => f ≫ k.base) e))).trans
        (AllFactorizationMixedTransport.postTail_inclusion l r X f))

omit [ModelCategory SSet.{v}] in
lemma tailTo_projection : tailTo f l r g e ≫ ResolutionLiftSpace.projection X V (f ≫ g.base) =
    ResolutionLiftSpace.projection X M (f ≫ l.base) := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun q => CoherentLiftPostComposition.tailMap X Y M V f l r ≫ q)
      (ResolutionLiftSpace.baseChange_projection (congrArg (fun k => f ≫ k.base) e))).trans
        (AllFactorizationMixedTransport.postTail_projection l r X f))

omit [ModelCategory SSet.{v}] in
lemma tailTo_post (b : V ⟶ W) (e' : l ≫ (r ≫ b) = g ≫ b) :
    tailTo f l r g e ≫ CoherentLiftPostComposition.tailMap X Y V W f g b =
      tailTo f l (r ≫ b) (g ≫ b) e' := by
  apply ResolutionLiftSpace.hom_ext
  · have hl := (Category.assoc (tailTo f l r g e)
        (CoherentLiftPostComposition.tailMap X Y V W f g b)
        (ResolutionLiftSpace.inclusion X W (f ≫ (g ≫ b).base))).trans
      (congrArg (fun q => tailTo f l r g e ≫ q)
        (AllFactorizationMixedTransport.postTail_inclusion g b X f))
    have ht := congrArg (fun q => q ≫
      (cosimplicialHom (ResolutionLiftSpace.frame X).obj).map b.diagram)
      (tailTo_inclusion f l r g e)
    have hm := congrArg (fun q => ResolutionLiftSpace.inclusion X M (f ≫ l.base) ≫ q)
      ((cosimplicialHom (ResolutionLiftSpace.frame X).obj).map_comp r.diagram b.diagram).symm
    exact hl.trans ((Category.assoc _ _ _).symm.trans
      (ht.trans ((Category.assoc _ _ _).trans (hm.trans (tailTo_inclusion f l (r ≫ b) _ e').symm))))
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun q => tailTo f l r g e ≫ q)
        (AllFactorizationMixedTransport.postTail_projection g b X f)).trans
          ((tailTo_projection f l r g e).trans (tailTo_projection f l (r ≫ b) _ e').symm))

omit [ModelCategory SSet.{v}] in
lemma boundary_cast {g h : Y ⟶ V} (e : g = h) :
    postBoundary X Y V f g ≫
      ResolutionLiftSpace.baseChange (congrArg (fun k => f ≫ k.base) e) =
        postBoundary X Y V f h := by
  cases e
  exact Category.comp_id _

omit [ModelCategory SSet.{v}] in
lemma choiceCast_postMap {g h : Y ⟶ V} (e : g = h) : PostCompositionChain.choiceCast f e =
    RelativeChoiceSpace.postMap (vertexInclusion X Y f) (postBoundary X Y V f g)
      (postBoundary X Y V f h)
      (ResolutionLiftSpace.baseChange (congrArg (fun k => f ≫ k.base) e)) (boundary_cast f e) := by
  cases e
  exact (RelativeChoiceSpace.postMap_identity _ _).symm

/-- Every prescribed point is transported exactly, before any homotopy is chosen. -/
lemma point_post (b : V ⟶ W) (p : ArrowFactorization g) :
    AllFactorizationComparison.point hcof f (g ≫ b)
        ((ArrowFactorization.postTo g b (g ≫ b) rfl).obj p) =
      AllFactorizationComparison.point hcof f g p ≫
        CoherentLiftPostComposition.firstMap hcof X Y V W f g b := by
  simp only [AllFactorizationComparison.point]
  rw [choiceCast_postMap, choiceCast_postMap]
  simp only [CoherentLiftPostComposition.firstMap]
  rw [RelativeChoiceSpace.postMap_ofExtension, RelativeChoiceSpace.postMap_ofExtension,
    RelativeChoiceSpace.postMap_ofExtension]
  refine RelativeChoiceSpace.ofExtension_congr _ _ _ _ _ _ ?_
  have ht := congrArg (fun q => postRight hcof X Y p.middle f p.left ≫ q)
    (tailTo_post f p.left p.right g p.fac b
      ((ArrowFactorization.postTo g b (g ≫ b) rfl).obj p).fac)
  let q := (ArrowFactorization.postTo g b (g ≫ b) rfl).obj p
  have hL := Category.assoc (postRight hcof X Y p.middle f p.left)
    (CoherentLiftPostComposition.tailMap X Y p.middle W f p.left (p.right ≫ b))
    (ResolutionLiftSpace.baseChange (congrArg (fun k => f ≫ k.base) q.fac))
  have hR := (congrArg (fun k => k ≫ CoherentLiftPostComposition.tailMap X Y V W f g b)
    (Category.assoc (postRight hcof X Y p.middle f p.left)
      (CoherentLiftPostComposition.tailMap X Y p.middle V f p.left p.right)
      (ResolutionLiftSpace.baseChange (congrArg (fun k => f ≫ k.base) p.fac)))).trans
        (Category.assoc _ _ _)
  exact hL.trans (ht.symm.trans hR.symm)

end SerrePositivity.HomotopyFunctionComplex.AllFactorizationPostPoints
