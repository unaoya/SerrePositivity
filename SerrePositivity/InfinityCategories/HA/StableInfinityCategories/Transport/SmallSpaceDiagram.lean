module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
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
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithful
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorEdgePointwise
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SimplexMarkedCover
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.EquivalenceDescent
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.InnerFibration
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.Reflection
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallSimplicialSet
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.UniverseVertexIso
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Localization
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SpaceDiagramImage

/-!
分割で生成：docstring を書き直すこと
 # 元の空間値図式を、同じ指定辺の反転を保って小さい全充満標的へ移す
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport
open _root_.SerrePositivity.KST.Fibration
variable {X : SSet.{u}} (F : (SSet.uliftFunctor.{u + 1, u}).obj X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})

/-- 元の全充満像の全単体を同じ小さい宇宙へ縮小した標的。 -/
def smallSpaceDiagramTarget : SSet.{u} := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallSimplicialSet.{u, u + 1} (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.spaceDiagramImage F)

/-- 小さい像の宇宙を戻し、元の空間の ∞ 圏へ含める。 -/
def smallSpaceDiagramInclusion :
    (SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.smallSpaceDiagramTarget F) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallSimplicialSetIso.{u, u + 1} (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.spaceDiagramImage F)).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.spaceDiagramImageInclusion F

/-- 元の全図式の小さい標的での表示。 -/
def smallSpaceDiagram : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.smallSpaceDiagramTarget F :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftMorphismDown
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.spaceDiagramImageLift F ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallSimplicialSetIso.{u, u + 1} (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.spaceDiagramImage F)).inv)

/-- 持ち上げた小さい図式の実包含との合成は、元の図式と厳密に一致する。 -/
theorem smallSpaceDiagram_inclusion :
    (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.smallSpaceDiagram F) ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.smallSpaceDiagramInclusion F = F := by
  let e : (SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.smallSpaceDiagramTarget F) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.spaceDiagramImage F := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallSimplicialSetIso.{u, u + 1} (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.spaceDiagramImage F)
  change (SSet.uliftFunctor.{u + 1, u}).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftMorphismDown (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.spaceDiagramImageLift F ≫ e.inv)) ≫
        (e.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.spaceDiagramImageInclusion F) = F
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftMorphismDown_lift]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun m => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.spaceDiagramImageLift F ≫ m)
      (Iso.inv_hom_id_assoc e (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.spaceDiagramImageInclusion F))).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.spaceDiagramImageLift_inclusion F))

/-- 持ち上げと充満忠実な後合成を通じた反転は、元の全辺の反転を反映する。 -/
theorem invertsEdges_of_ulift_post {Y Z : SSet.{u}} [Quasicategory Z]
    (f : Y ⟶ Z) (j : (SSet.uliftFunctor.{u + 1, u}).obj Z ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (hj : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful j) (W : Set (Y _⦋1⦌))
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges ((SSet.uliftFunctor.{u + 1, u}).map f ≫ j) (ULift.up '' W)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges f W := by
  intro s hs
  have he := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.invertedEdges_comp_iff ((SSet.uliftFunctor.{u + 1, u}).map f) j
    (ULift.up s)).mp (hf (Set.mem_image_of_mem ULift.up hs))
  have hr := hj.reflects_isInvertibleEdge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (((SSet.uliftFunctor.{u + 1, u}).map f).app
      (Opposite.op ⦋1⦌) (ULift.up s))) he
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (show
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.downTruncatedEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (((SSet.uliftFunctor.{u + 1, u}).map f).app
      (Opposite.op ⦋1⦌) (ULift.up s)))).edge =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s).map ((truncation 2).map f)).edge from rfl)).mp hr.down

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.invertsEdges_of_ulift_post := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.invertsEdges_of_ulift_post

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.smallSpaceDiagram (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.smallSpaceDiagram := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.smallSpaceDiagram

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.smallSpaceDiagramInclusion (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.smallSpaceDiagramInclusion := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.smallSpaceDiagramInclusion

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.smallSpaceDiagramTarget (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.smallSpaceDiagramTarget := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.smallSpaceDiagramTarget

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.smallSpaceDiagram_inclusion := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.smallSpaceDiagram_inclusion
