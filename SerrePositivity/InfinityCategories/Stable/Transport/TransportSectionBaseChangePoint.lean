module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Diagrams.RelativeSectionDiagram
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationBaseChange
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationInfinity
public import SerrePositivity.InfinityCategories.F1.Transport.SimplexDomains
public import SerrePositivity.InfinityCategories.F1.Transport.SimplexFirstVertexNaturality
public import SerrePositivity.InfinityCategories.F1.Transport.SimplexSectionBaseChange
public import SerrePositivity.InfinityCategories.F1.Transport.SimplexSectionDiagram

/-!
分割で生成：docstring を書き直すこと
 # 全単体の切断の指定底変換同型は、元の pullback 係数成分を保つ
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Stable.Transport
open SerrePositivity.KST.Fibration
variable {B D : SSet.{u}} (k : D ⟶ B)

/-- 全単体上の底変換同型は、元の相対切断の共同同型の端点だけを表示変更する。 -/
theorem transportSimplexSectionInfinity_baseChangeIso_heq :
    HEq (transportSimplexSectionInfinity_baseChangeIso k)
      (relativeSectionDiagramInfinityBaseChangeIso k (transportSimplexDomainFunctor D)) := by
  unfold transportSimplexSectionInfinity_baseChangeIso
  dsimp only [transportSimplexSectionInfinity]
  have hcast {α β : Sort (u + 2)} (h : β = α) (x : α) : HEq (Eq.mpr h x) x := by
    cases h
    rfl
  let A := transportSimplexDomainFunctor D
  let P := (pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u}
  have hm := hcast (congrArg
    (fun M => FunctorIso (relativeSectionDiagramInfinity A ≫ P)
      (relativeSectionDiagramInfinity M)) (transportSimplexDomainFunctor_baseChange k))
    (relativeSectionDiagramInfinityBaseChangeIso k A)
  exact (hcast _ _).trans hm

end SerrePositivity.InfinityCategories.Stable.Transport

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.transportSimplexSectionInfinity_baseChangeIso_heq := _root_.SerrePositivity.InfinityCategories.Stable.Transport.transportSimplexSectionInfinity_baseChangeIso_heq
