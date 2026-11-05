module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Enriched.Basic
public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Diagrams.RelativeSectionDiagram
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationInfinity
public import SerrePositivity.InfinityCategories.F1.KanModels.KanEnrichedDiagram
public import SerrePositivity.InfinityCategories.F1.Transport.SimplexDomains
public import SerrePositivity.InfinityCategories.F1.Transport.SimplexFirstVertexNaturality
public import SerrePositivity.InfinityCategories.F1.Transport.SimplexSectionBaseChange

/-!
分割で生成：docstring を書き直すこと
 # 像の単体での指定切断比較を、元の左底変換比較の端点へ揃える
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Stable.Straightening
open SerrePositivity.KST.Fibration
variable {B D : SSet.{u}} (k : D ⟶ B)

/-- 全単体の底変換は、同じ像の単体における切断 Kan 対象を回収する。 -/
theorem straighteningBaseChangeLeft_section_eq
    (X : LeftFibrationObject B) (c : TransportSimplexCategory D) :
    (((relativeSectionEnrichedDiagram
      (transportSimplexDomainFunctor D ⋙ Over.map k)).obj c).obj X) =
      (((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).obj
        ((transportSimplexFunctor k).obj c)).obj X) :=
  (congrArg (fun A => ((relativeSectionEnrichedDiagram A).obj c).obj X)
    (transportSimplexDomainFunctor_baseChange k)).symm

end SerrePositivity.InfinityCategories.Stable.Straightening

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.straighteningBaseChangeLeft_section_eq := _root_.SerrePositivity.InfinityCategories.Stable.Straightening.straighteningBaseChangeLeft_section_eq
