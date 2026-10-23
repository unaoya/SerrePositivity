module
public import SerrePositivity.KST.Fibration.SpaceDiagramImage
public import SerrePositivity.KST.Fibration.QuasicategoryUniverseReflection
public import SerrePositivity.InfinityCategories.F1.Universe.EquivalenceDescent
public import SerrePositivity.InfinityCategories.Stable.UniverseVertexIso
public import SerrePositivity.InfinityCategories.Core.FunctorEdgePointwise
public import SerrePositivity.InfinityCategories.F1.Diagrams.LocalizationSourceIso

/-! # 元の空間値図式を、同じ指定辺の反転を保って小さい全充満標的へ移す -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {X : SSet.{u}} (F : (SSet.uliftFunctor.{u + 1, u}).obj X ⟶ SpaceInfinity.{u})

/-- 元の全充満像の全単体を同じ小さい宇宙へ縮小した標的。 -/
def smallSpaceDiagramTarget : SSet.{u} := smallSimplicialSet.{u, u + 1} (spaceDiagramImage F)

instance smallSpaceDiagramTarget_quasicategory : Quasicategory (smallSpaceDiagramTarget F) :=
  smallSimplicialSet_quasicategory.{u, u + 1} _

/-- 小さい像の宇宙を戻し、元の空間の ∞ 圏へ含める。 -/
def smallSpaceDiagramInclusion :
    (SSet.uliftFunctor.{u + 1, u}).obj (smallSpaceDiagramTarget F) ⟶ SpaceInfinity.{u} :=
  (smallSimplicialSetIso.{u, u + 1} (spaceDiagramImage F)).hom ≫ spaceDiagramImageInclusion F

/-- 元の全図式の小さい標的での表示。 -/
def smallSpaceDiagram : X ⟶ smallSpaceDiagramTarget F :=
  uliftMorphismDown
    (spaceDiagramImageLift F ≫ (smallSimplicialSetIso.{u, u + 1} (spaceDiagramImage F)).inv)

/-- 持ち上げた小さい図式の実包含との合成は、元の図式と厳密に一致する。 -/
theorem smallSpaceDiagram_inclusion :
    (SSet.uliftFunctor.{u + 1, u}).map (smallSpaceDiagram F) ≫
      smallSpaceDiagramInclusion F = F := by
  let e : (SSet.uliftFunctor.{u + 1, u}).obj (smallSpaceDiagramTarget F) ≅
      spaceDiagramImage F := smallSimplicialSetIso.{u, u + 1} (spaceDiagramImage F)
  change (SSet.uliftFunctor.{u + 1, u}).map
      (uliftMorphismDown (spaceDiagramImageLift F ≫ e.inv)) ≫
        (e.hom ≫ spaceDiagramImageInclusion F) = F
  rw [uliftMorphismDown_lift]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun m => spaceDiagramImageLift F ≫ m)
      (Iso.inv_hom_id_assoc e (spaceDiagramImageInclusion F))).trans
        (spaceDiagramImageLift_inclusion F))

/-- 小さい標的の包含は、元の全写像空間の意味で充満忠実。 -/
theorem smallSpaceDiagramInclusion_isFullyFaithful :
    IsFullyFaithful (smallSpaceDiagramInclusion F) :=
  (qCatEquivalenceOfIso (smallSimplicialSetIso.{u, u + 1} (spaceDiagramImage F))).isQCatEquivalence
    |>.isFullyFaithful |>.comp (spaceDiagramImageInclusion_isFullyFaithful F)

/-- 持ち上げと充満忠実な後合成を通じた反転は、元の全辺の反転を反映する。 -/
theorem invertsEdges_of_ulift_post {Y Z : SSet.{u}} [Quasicategory Z]
    (f : Y ⟶ Z) (j : (SSet.uliftFunctor.{u + 1, u}).obj Z ⟶ SpaceInfinity.{u})
    (hj : IsFullyFaithful j) (W : Set (Y _⦋1⦌))
    (hf : InvertsEdges ((SSet.uliftFunctor.{u + 1, u}).map f ≫ j) (ULift.up '' W)) :
    InvertsEdges f W := by
  intro s hs
  have he := (invertedEdges_comp_iff ((SSet.uliftFunctor.{u + 1, u}).map f) j
    (ULift.up s)).mp (hf (Set.mem_image_of_mem ULift.up hs))
  have hr := hj.reflects_isInvertibleEdge
    (edgeOfSimplex (((SSet.uliftFunctor.{u + 1, u}).map f).app
      (Opposite.op ⦋1⦌) (ULift.up s))) he
  exact (isInvertibleEdge_congr (show
    (downTruncatedEdge (edgeOfSimplex (((SSet.uliftFunctor.{u + 1, u}).map f).app
      (Opposite.op ⦋1⦌) (ULift.up s)))).edge =
      ((edgeOfSimplex s).map ((truncation 2).map f)).edge from rfl)).mp hr.down

/-- 元の図式による反転は、同じ辺の宇宙降下と全充満包含の反映で小さい図式へ移る。 -/
theorem smallSpaceDiagram_inverts (W : Set (X _⦋1⦌))
    (hF : InvertsEdges F (ULift.up '' W)) : InvertsEdges (smallSpaceDiagram F) W := by
  apply invertsEdges_of_ulift_post (smallSpaceDiagram F) (smallSpaceDiagramInclusion F)
    (smallSpaceDiagramInclusion_isFullyFaithful F) W
  rw [smallSpaceDiagram_inclusion]
  exact hF

end SerrePositivity.KST.Fibration
