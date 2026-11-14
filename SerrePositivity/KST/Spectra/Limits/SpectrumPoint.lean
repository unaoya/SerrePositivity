module
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Opposite
public import Mathlib.Basic.UnivLE
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.EpiMono
public import Mathlib.CategoryTheory.Extensive
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.WalkingPair
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
public import Mathlib.CategoryTheory.Limits.Shapes.StrongEpi
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Logic.Equiv.Defs
public import SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.SuspensionLoop
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.SpectrumPoint
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyIso
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.HomotopyIsomorphism
public import SerrePositivity.KST.Spectra.OmegaSpectrum
public import SerrePositivity.KST.Spectra.SuspensionLoop
public import SerrePositivity.Spectra.Pointed.Basic
public import SerrePositivity.Spectra.PointedSimplicialSet.Basic


/-!
分割で生成：docstring を書き直すこと
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
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 概要：各段が一点の実際の Ω スペクトル。
方針：懸垂構造射とその随伴が零対象間の同型であることを使う。
規約：全基点・零次数を含む Ω 条件と単射な構造射を持つ。
使われ方：BF 1978 §2、Sp の空積の頂点。 -/
def spectrumPoint : OmegaSpectrum.{u} where
  level _ := ⟨PointedObject.point, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedPoint_kanComplex⟩
  sigma _ := PointedObject.toPoint _
  sigma_mono _ := by
    have := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.suspensionPoint_isZero.isIso PointedObject.point_isZero (PointedObject.toPoint _)
    change Mono (PointedSimplicialSet.forget.map (PointedObject.toPoint
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (PointedObject.point : PointedSimplicialSet.{u}))))
    infer_instance
  omega_condition _ := by
    let f := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv (PointedObject.point : PointedSimplicialSet.{u}) _
      (PointedObject.toPoint _)
    have := PointedObject.point_isZero.isIso _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.loopPoint_isZero f
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanPiIsomorphism.of_iso (X := (PointedObject.point : PointedSimplicialSet.{u}).right)
      (Y := (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (PointedObject.point : PointedSimplicialSet.{u})).right)
      (PointedSimplicialSet.forget.mapIso (asIso f))

end
end SerrePositivity.InfinityCategories.HomotopyLimits
