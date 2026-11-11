module

public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Logic.Equiv.Defs
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceRightKan
public import SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.SuspensionLoop
public import SerrePositivity.Spectra.Pointed.Basic
public import SerrePositivity.Spectra.PointedSimplicialSet.Basic

/-!
概要：各段が一点の Ω スペクトル。
方針：懸垂と loop の随伴と一点の零対象性から構造射とその随伴の同型性を得る。
規約：L9 の単射構造射と全基点の Ω 条件を備える実際の対象を使う。
使われ方：BF 1978 §2、HA §1.4.2、HTT 4.2.4.1 の Sp の空積。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 概要：点つき一点単体集合は Kan。
方針：基礎単体集合が終対象であることを使う。
規約：PointedObject.point の既存の定義を用いる。
使われ方：一点スペクトルの各段の Kan 条件。 -/
instance pointedPoint_kanComplex :
    KanComplex (PointedObject.point : PointedSimplicialSet.{u}).right := by
  change KanComplex (𝟙_ SSet.{u})
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.kanComplex_of_rightHornFillers
  intro n i _ σ
  exact ⟨CartesianMonoidalCategory.isTerminalTensorUnit.from _,
    CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext _ _⟩

/-- 概要：一点の懸垂は点つき単体集合の零対象。
方針：随伴によって一点からの射の一意性を移し、初対象として一点と同型にする。
規約：通常の smash による懸垂を使う。
使われ方：一点スペクトルの構造射の単射性。 -/
lemma suspensionPoint_isZero :
    IsZero (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (PointedObject.point : PointedSimplicialSet.{u})) := by
  have h : IsInitial (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (PointedObject.point : PointedSimplicialSet.{u})) :=
    IsInitial.ofUniqueHom (fun Y ↦ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ Y).symm 0)
      (fun Y f ↦ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ Y).injective (PointedObject.point_isZero.eq_of_src _ _))
  exact PointedObject.point_isZero.of_iso
    (h.uniqueUpToIso PointedObject.point_isZero.isInitial)

/-- 概要：一点の loop は点つき単体集合の零対象。
方針：随伴によって一点への射の一意性を移し、終対象として一点と同型にする。
規約：円からの点つき内部 Hom を使う。
使われ方：一点スペクトルの全基点の Ω 条件。 -/
lemma loopPoint_isZero :
    IsZero (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (PointedObject.point : PointedSimplicialSet.{u})) := by
  have h : IsTerminal (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (PointedObject.point : PointedSimplicialSet.{u})) :=
    IsTerminal.ofUniqueHom (fun Y ↦ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv Y _ 0)
      (fun Y f ↦ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv Y _).symm.injective
        (PointedObject.point_isZero.eq_of_tgt _ _))
  exact PointedObject.point_isZero.of_iso
    (h.uniqueUpToIso PointedObject.point_isZero.isTerminal)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
