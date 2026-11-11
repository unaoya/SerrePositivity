module
public import SerrePositivity.KST.SConstruction.ZeroRowKanFiberComparison
public import SerrePositivity.KST.SConstruction.BoundaryPointedComparison
public import SerrePositivity.KST.SConstruction.MultiSTrivialFibration

/-! # 元の点つき経路零行と前段の Kan 反復実現の比較
概要：S₁ の完全な比較と全零境界商を通して、零行の Kan 模型から前段への全基点 π_* 同型を構成する。
方針：零行の選んだ基点の像を前段の実現の基点にし、既存の任意頂点からの境界商比較を使う。
規約：既存の前段の Kan 模型を標的にする。使われ方：前段と homotopy fiber の共通比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.SimplicialModel SerrePositivity.InfinityCategories
open Spectra
open scoped Simplicial

/-- 元の経路零行から前の反復実現への S₁ 比較。 -/
def zeroRowPreviousComparison (r : ℕ) (X : StableModel.{u}) :
    (iteratedPathRealizationDiagram r X).obj (Opposite.op ⦋0⦌) ⟶
      multiDiagonalCoreSConstruction r X :=
  (multiRealizationFunctor r).map (stableSOneComparison X)

/-- 元の零行の S₁ 比較は全ての有限反復で局所化同型。 -/
lemma zeroRowPreviousComparison_localized_isIso (r : ℕ) (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (zeroRowPreviousComparison r X)) := by
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (stableSOneComparison X).val :=
    inferInstanceAs (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (sOneComparison X.carrier))
  exact multiRealizationFunctor_map_localized_isIso r (stableSOneComparison X)

/-- 元の点つき経路零行から前段の全零境界商の Kan 模型への射。 -/
def zeroRowPointedPreviousComparison (r : ℕ) (X : StableModel.{u})
    (b : ((iteratedSRealizationDiagram (r + 1) X).obj (Opposite.op ⦋0⦌)) _⦋0⦌) :
    zeroRowPointedModel (r + 1) X b ⟶ (boundaryKanRealizationFunctor r).obj X := by
  let A := zeroRowPointedModel (r + 1) X b
  let f := zeroRowPreviousComparison (r + 1) X
  let x := f.app (Opposite.op ⦋0⦌) A.basepoint
  let g : A ⟶ PointedSimplicialSet.ofVertex (multiDiagonalCoreSConstruction (r + 1) X) x :=
    pointedHomOfBasepoint f (by rw [PointedSimplicialSet.basepoint_ofVertex]; rfl)
  exact g ≫ boundaryReductionPointedMap r X x ≫
    PointedKanReplacement.unit.app (boundaryReducedRealization r X)

/-- 前段への元の点つき零行比較は局所化同型。 -/
lemma zeroRowPointedPreviousComparison_localized_isIso (r : ℕ) (X : StableModel.{u})
    (b : ((iteratedSRealizationDiagram (r + 1) X).obj (Opposite.op ⦋0⦌)) _⦋0⦌) :
    IsIso (AnodyneHomotopy.anodyneQ.map (zeroRowPointedPreviousComparison r X b).right) := by
  let Q := AnodyneHomotopy.anodyneQ
  have hf := zeroRowPreviousComparison_localized_isIso (r + 1) X
  have hq := boundaryReductionQuotient_image_isIso Q
    (Localization.inverts Q anodyneExtensions) r X
  have hu : IsIso (Q.map (PointedKanReplacement.unit.app (boundaryReducedRealization r X)).right) :=
    (Localization.inverts Q anodyneExtensions) _ (PointedKanReplacement.unit_anodyne _)
  change IsIso (Q.map (zeroRowPreviousComparison (r + 1) X ≫ boundaryReductionQuotient r X ≫
    (PointedKanReplacement.unit.app (boundaryReducedRealization r X)).right))
  rw [Q.map_comp, Q.map_comp]
  infer_instance

/-- 点つき零行の共通 Kan 模型から前段の既存の Kan 実現への厳密な延長。 -/
def zeroRowKanPreviousComparison (r : ℕ) (X : StableModel.{u})
    (b : ((iteratedSRealizationDiagram (r + 1) X).obj (Opposite.op ⦋0⦌)) _⦋0⦌) :
    PointedKanReplacement.obj (zeroRowPointedModel (r + 1) X b) ⟶
      (boundaryKanRealizationFunctor r).obj X :=
  pointedKanStrictExtension (zeroRowPointedPreviousComparison r X b)

/-- 共通 Kan 模型から前段の既存の Kan 実現への比較は全基点 π_* 同型。 -/
lemma zeroRowKanPreviousComparison_piIsomorphism (r : ℕ) (X : StableModel.{u})
    (b : ((iteratedSRealizationDiagram (r + 1) X).obj (Opposite.op ⦋0⦌)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (zeroRowKanPreviousComparison r X b).right :=
  pointedKanStrictExtension_piIsomorphism (zeroRowPointedPreviousComparison r X b)
    (zeroRowPointedPreviousComparison_localized_isIso r X b)

end SerrePositivity.KST.SConstruction
