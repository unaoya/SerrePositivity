module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementReedyLeftAnodyne
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementDiagonal
public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalLeftAnodyne

/-!
概要：simplicial replacementは各成分のleft anodyne性を元の全写像へ送る。
方針：元のbarのReedy left anodyne性を対角へ送り、指定された同じ写像へ全同型で運ぶ。
規約：元のsimplicialReplacementMapそのものの性質。条件の弱化や模型の変更をしない。
使われ方：IS-W2 R03f.2、元のEx∞係数の単位の相対的な比較。
-/
@[expose] public noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.BisimplicialModel

/-- R03f.2：元の各係数射がleft anodyneなら、同じsimplicial replacementの全写像もleft anodyne。 -/
theorem simplicialReplacementMap_leftAnodyne
    {I : Type u} [SmallCategory I] {F G : I ⥤ SSet.{u}}
    (η : F ⟶ G) (hη : ∀ i, leftAnodyneExtensions (η.app i)) :
    leftAnodyneExtensions (simplicialReplacementMap η) := by
  have h := diagonal_map_leftAnodyne (simplicialReplacementRowsMap η)
    (simplicialReplacementRowsMap_reedy_leftAnodyne η hη)
  exact (leftAnodyneExtensions.arrow_mk_iso_iff
    (Arrow.isoMk (simplicialReplacementDiagonalIso F) (simplicialReplacementDiagonalIso G)
      (simplicialReplacementDiagonalIso_naturality η).symm)).mp h

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
