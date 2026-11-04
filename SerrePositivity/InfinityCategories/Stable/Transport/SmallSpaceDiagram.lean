module
public import Mathlib.AlgebraicTopology.Quasicategory.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.CompStructTruncated
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import SerrePositivity.InfinityCategories.Core.FullyFaithful
public import SerrePositivity.InfinityCategories.Core.FunctorEdgePointwise
public import SerrePositivity.InfinityCategories.Core.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Transport.SimplexMarkedCover
public import SerrePositivity.InfinityCategories.F1.Universe.EquivalenceDescent
public import SerrePositivity.InfinityCategories.F1.Universe.InnerFibration
public import SerrePositivity.InfinityCategories.F1.Universe.Reflection
public import SerrePositivity.InfinityCategories.F1.Universe.SmallSimplicialSet
public import SerrePositivity.InfinityCategories.F1.UniverseVertexIso
public import SerrePositivity.InfinityCategories.F1B.Localization.Localization
public import SerrePositivity.InfinityCategories.F1.Transport.SpaceDiagramImage

/-!
分割で生成：docstring を書き直すこと
 # 元の空間値図式を、同じ指定辺の反転を保って小さい全充満標的へ移す
-/

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

end SerrePositivity.KST.Fibration
