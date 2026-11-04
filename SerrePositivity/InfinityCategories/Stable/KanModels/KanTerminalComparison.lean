module
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialNerve
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
public import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.OfMap
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization
public import SerrePositivity.InfinityCategories.Coherent.Quasicategory
public import SerrePositivity.InfinityCategories.Core.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Core.Terminal
public import SerrePositivity.InfinityCategories.Core.TerminalTransport
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Categories.PointedSpaces
public import SerrePositivity.InfinityCategories.F1.Coherent.Edges
public import SerrePositivity.InfinityCategories.F1.Coherent.KanInvertible
public import SerrePositivity.InfinityCategories.F1.Coherent.Vertices
public import SerrePositivity.InfinityCategories.F1.KanModels.KanAnodyneLocalization
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpaceTerminal

/-!
分割で生成：docstring を書き直すこと
 # 元の一点射の可逆性から、同じ Ex∞ 値の空間の ∞ 圏での終対象性へ接続する
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.InfinityCategories.HomotopyLimits
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.Comparison
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 元の Kan 値の一点射が可逆なら、同じ元の空間の頂点は終対象である。 -/
theorem kanVertex_isTerminal_of_localized_toPoint (K : KanObject.{u})
    (hK : IsIso (AnodyneHomotopy.anodyneQ.map (terminal.from K.obj))) :
    IsTerminalVertex (coherentNerveVertex K) := by
  let Q := AnodyneHomotopy.anodyneQ.{u}
  let f : K ⟶ pointKanObject.{u} := stdSimplex.isTerminalObj₀.from K.obj
  have hp : IsIso (terminal.from pointKanObject.{u}.obj) :=
    isIso_of_isTerminal stdSimplex.isTerminalObj₀ terminalIsTerminal _
  have he : (show K.obj ⟶ pointKanObject.{u}.obj from f) ≫
      terminal.from pointKanObject.{u}.obj = terminal.from K.obj := terminal.hom_ext _ _
  have hf : IsIso (Q.map (show K.obj ⟶ pointKanObject.{u}.obj from f)) := by
    have hc : IsIso (Q.map (show K.obj ⟶ pointKanObject.{u}.obj from f) ≫
        Q.map (terminal.from pointKanObject.{u}.obj)) := by
      rw [← Functor.map_comp, he]
      exact hK
    exact (isIso_comp_right_iff _ _).mp hc
  have hi : IsInvertibleEdge (coherentNerveEdge f) :=
    coherentKanEdge_isInvertible_of_isQCatEquivalence (K := K) (L := pointKanObject.{u})
      (isQCatEquivalence_of_anodyneQ_isIso (show K.obj ⟶ pointKanObject.{u}.obj from f) hf)
  have : IsIso (Truncated.HomotopyCategory.homMk (coherentNerveEdge f).toTruncated) := hi
  have ht : IsTerminalVertex (coherentNerveVertex pointKanObject.{u}) := by
    simpa only [pointSpaceVertex, spaceInfinityVertex_eq_coherent] using
      pointSpaceVertex_isTerminalVertex.{u}
  exact ht.of_vertexIso (asIso
    (Truncated.HomotopyCategory.homMk (coherentNerveEdge f).toTruncated)).symm

end SerrePositivity.KST.Fibration
