module
public import SerrePositivity.KST.SConstruction.ZeroRowCartesianComparison
public import SerrePositivity.KST.SConstruction.IteratedBoundaryKanComparison

/-! # 零行から既存の Kan 境界の基点 fiber への四角形
概要：元の零行から既存の点つき Kan 経路全空間への射は、基点と境界に関する homotopy pullback を与える。
方針：元の零列四角形を二つの Kan 比較と可縮な S₀ 行の終射で移す。
規約：零行を別模型に置換せず元の射を使う。使われ方：既存の path homotopy fiber への比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.SimplicialModel SerrePositivity.KST.Comparison
open scoped Simplicial

/-- 元の経路零行から既存の点つき Kan 経路全空間への射。 -/
def zeroRowPathToKan (r : ℕ) (X : StableModel.{u}) :
    (iteratedPathRealizationDiagram r X).obj (Opposite.op ⦋0⦌) ⟶
      ((pointedIteratedPathKanFunctor r).obj X).right :=
  diagonalZeroColumn (iteratedPathRealizationDiagram r X) ≫ iteratedPathToKan r X

/-- 元の経路零行の境界は既存の Kan 標的の基点に厳密に定数。 -/
lemma zeroRowPathToKan_boundary (r : ℕ) (X : StableModel.{u}) :
    zeroRowPathToKan r X ≫ (pointedFullIteratedPathKanBoundary r X).right =
      toUnit ((iteratedPathRealizationDiagram r X).obj (Opposite.op ⦋0⦌)) ≫
        ((boundaryKanRealizationFunctor r).obj X).hom := by
  have he : diagonalZeroColumn (iteratedPathRealizationDiagram r X) ≫
      iteratedPathRealizationBoundary r X =
    (iteratedPathBoundary r X).app (Opposite.op ⦋0⦌) ≫
      diagonalZeroColumn (iteratedSRealizationDiagram r X) :=
    (diagonalZeroColumnNat.naturality (iteratedPathBoundary r X)).symm
  change (diagonalZeroColumn _ ≫ iteratedPathToKan r X) ≫ _ = _
  rw [Category.assoc, ← iteratedBoundaryToKan_comm, ← Category.assoc, he, Category.assoc,
    iteratedRealizationToKan_zeroColumn, ← Category.assoc, comp_toUnit]

/-- 元の零行と既存の点つき Kan 境界の基点の四角形は正の全反復で homotopy pullback。 -/
lemma zeroRowKanBoundary_homotopyPullback (r : ℕ) (X : StableModel.{u}) :
    IsHomotopyPullback (CommSq.mk (zeroRowPathToKan_boundary (r + 1) X)) := by
  let A := (iteratedPathRealizationDiagram (r + 1) X).obj (Opposite.op ⦋0⦌)
  let B := (iteratedSRealizationDiagram (r + 1) X).obj (Opposite.op ⦋0⦌)
  have hB : IsIso (AnodyneHomotopy.anodyneQ.map (toUnit B)) :=
    multiRealization_toPoint_localized_isIso_of_contractible (r + 1) (sStableModel 0 X)
      (sConstructionZero_isContractibleKan X.carrier)
  apply (isHomotopyPullback_iff_of_localized_isIso
    (CommSq.mk ((diagonalZeroColumnNat.naturality
      (iteratedPathBoundary (r + 1) X)).symm))
    (CommSq.mk (zeroRowPathToKan_boundary (r + 1) X))
    (𝟙 A) (iteratedPathToKan (r + 1) X) (toUnit B) (iteratedRealizationToKan (r + 1) X)
    ?_ ?_ ?_ ?_ (by exact (AnodyneHomotopy.anodyneQ.mapIso (Iso.refl A)).isIso_hom)
    (iteratedPathToKan_localized_isIso (r + 1) X)
    hB (iteratedRealizationToKan_localized_isIso (r + 1) X)).mp
      (iteratedPathBoundary_zeroRow_homotopyPullback r X)
  · exact (Category.id_comp _).symm
  · exact isTerminalTensorUnit.hom_ext _ _
  · exact iteratedBoundaryToKan_comm (r + 1) X
  · exact iteratedRealizationToKan_zeroColumn (r + 1) X

end SerrePositivity.KST.SConstruction
