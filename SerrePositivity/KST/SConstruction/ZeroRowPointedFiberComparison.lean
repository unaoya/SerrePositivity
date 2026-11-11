module
public import SerrePositivity.KST.SConstruction.PathZeroColumnSection

/-! # 零段の任意の頂点から定める点つき零行の fiber 比較
概要：零段の頂点を退化で経路零行へ写して基点とし、既存の fiber への比較を点つきにする。
方針：退化像は定数 path と全空間の基点へ写るので、引き戻しの両射影で基点を照合する。
規約：零対象の新しい保存仮定は不要。使われ方：零行の Kan 置換と全基点 π_* 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.SimplicialModel
open Spectra
open scoped Simplicial

/-- 零段の退化像は元の零行 fiber 比較で既存の fiber の基点へ厳密に潰れる。 -/
lemma zeroRowPathFiberComparison_degeneracy (r : ℕ) (X : StableModel.{u}) :
    (iteratedSRealizationDiagram r X).map (SimplexCategory.σ (0 : Fin 1)).op ≫
      zeroRowPathFiberComparison r X =
        toUnit ((iteratedSRealizationDiagram r X).obj (Opposite.op ⦋0⦌)) ≫
          (iteratedPathHomotopyFiber r X).hom := by
  let f := pointedFullIteratedPathKanBoundary r X
  have hp : (iteratedPathHomotopyFiber r X).hom ≫
      (pullback.fst (pathEndpoint ((boundaryKanRealizationFunctor r).obj X)) f).right =
    (basedPathSpace ((boundaryKanRealizationFunctor r).obj X)).hom :=
    Under.w (pullback.fst (pathEndpoint ((boundaryKanRealizationFunctor r).obj X)) f)
  have he : (iteratedPathHomotopyFiber r X).hom ≫
      (pullback.snd (pathEndpoint ((boundaryKanRealizationFunctor r).obj X)) f).right =
      ((pointedIteratedPathKanFunctor r).obj X).hom := Under.w (pullback.snd _ f)
  have hpr : zeroRowPathFiberComparison r X ≫
      (pullback.snd (pathEndpoint ((boundaryKanRealizationFunctor r).obj X)) f).right =
    zeroRowPathToKan r X := zeroRowPathFiberComparison_projection r X
  apply (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedPullback_isPullback
    (pathEndpoint ((boundaryKanRealizationFunctor r).obj X)) f).hom_ext
  · rw [Category.assoc]
    change _ ≫ (strictZeroPathFiberMap f (zeroRowPathToKan r X) _ ≫ _) = _
    rw [strictZeroPathFiberMap_path, ← Category.assoc, comp_toUnit, Category.assoc, hp]
  · rw [Category.assoc, hpr,
      zeroRowPathToKan_degeneracy, Category.assoc, he]

/-- 元の零段の頂点の退化を基点に取った経路零行。 -/
def zeroRowPointedModel (r : ℕ) (X : StableModel.{u})
    (b : ((iteratedSRealizationDiagram r X).obj (Opposite.op ⦋0⦌)) _⦋0⦌) :
    PointedSimplicialSet.{u} :=
  PointedSimplicialSet.ofVertex ((iteratedPathRealizationDiagram r X).obj (Opposite.op ⦋0⦌))
    (((iteratedSRealizationDiagram r X).map (SimplexCategory.σ (0 : Fin 1)).op).app _ b)

/-- 元の点つき零行から既存の path homotopy fiber への比較。 -/
def zeroRowPointedFiberComparison (r : ℕ) (X : StableModel.{u})
    (b : ((iteratedSRealizationDiagram r X).obj (Opposite.op ⦋0⦌)) _⦋0⦌) :
    zeroRowPointedModel r X b ⟶ iteratedPathHomotopyFiber r X :=
  Under.homMk (zeroRowPathFiberComparison r X) (by
    change SSet.const _ ≫ zeroRowPathFiberComparison r X = _
    rw [← SSet.const_comp b ((iteratedSRealizationDiagram r X).map
      (SimplexCategory.σ (0 : Fin 1)).op), Category.assoc,
      zeroRowPathFiberComparison_degeneracy, ← Category.assoc, comp_toUnit]
    rfl)

/-- 任意の零段基点に対する点つき零行 fiber 比較は正の全反復で局所化同型。 -/
lemma zeroRowPointedFiberComparison_localized_isIso (r : ℕ) (X : StableModel.{u})
    (b : ((iteratedSRealizationDiagram (r + 1) X).obj (Opposite.op ⦋0⦌)) _⦋0⦌) :
    IsIso (AnodyneHomotopy.anodyneQ.map (zeroRowPointedFiberComparison (r + 1) X b).right) :=
  zeroRowPathFiberComparison_localized_isIso r X

end SerrePositivity.KST.SConstruction
