module
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationBaseChange
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationInfinity
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningAllBases
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningBaseChange
public import SerrePositivity.InfinityCategories.F1.Transport.SimplexDomains
public import SerrePositivity.InfinityCategories.F1.Transport.SimplexFirstVertex
public import SerrePositivity.InfinityCategories.F1.Transport.SimplexFirstVertexNaturality
public import SerrePositivity.InfinityCategories.F1.Transport.SimplexSectionBaseChange
public import SerrePositivity.InfinityCategories.F1.Transport.SimplexSectionDiagram

/-!
分割で生成：docstring を書き直すこと
 # 同じ straightening 底変換同型を全単体へ戻すと、元の指定比較を回収する
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {B D : SSet.{u}} (k : D ⟶ B)

/-- 元の大域底変換の定義で選んだ、同じ全単体上の制限比較を明示する。 -/
def straighteningJointBaseChangeRestrictionIso :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap D) ≫
        ((SSet.uliftFunctor.{u + 1, u}).map k ≫ leftStraighteningSectionJointDiagram B))
      ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap D) ≫
        (leftStraighteningSectionJointDiagram D ≫
          (pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u})) := by
  let U := SSet.uliftFunctor.{u + 1, u}
  let t := U.map (nerveMap (transportSimplexFunctor k))
  let l := U.map (transportSimplexFirstVertexMap D)
  let P := (pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u}
  have hleft : l ≫ (U.map k ≫ leftStraighteningSectionJointDiagram B) =
      t ≫ (U.map (transportSimplexFirstVertexMap B) ≫
        leftStraighteningSectionJointDiagram B) := by
    rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality k, Category.assoc]
  exact eqToIso (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) hleft) ≪≫
    (leftStraighteningSectionJointDiagram_restrictIso B).precomp t ≪≫
    (transportSimplexSectionInfinity_baseChangeIso k).symm ≪≫
    ((leftStraighteningSectionJointDiagram_restrictIso D).postcomp P).symm

end SerrePositivity.KST.Fibration
