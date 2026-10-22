module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellNativeRoofSquare
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovClassProReflection

/-!
概要：class 比較と有界商射で、実三角形付き roof の逆を元の有限切断へ反映する。
方針：元の準同型正方形で右の実経路を反映し、左の実持ち上げを cell 細分で保つ。
規約：局所化の等式から実経路を仮定しない。使われ方：元の一切断射への roof 抽出。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)

lemma postnikovClassModelMap_reflects_cellNativeRoofProInverse (n : ℤ) (hn : 0 ≤ n)
    (hf : HasCellNativeRoofProInverse R
      (f.map (postnikovClassModelFunctor R n hn))) :
    HasCellNativeRoofProInverse R (f.map (postnikovFunctor R (n + 1))) := by
  let a := TowerDiagram.mapNat A (postnikovClassModelComparison R n hn)
  let b := TowerDiagram.mapNat B (postnikovClassModelComparison R n hn)
  apply HasCellNativeRoofProInverse.of_square R _ _ a b ?_ ?_ ?_ hf
  · apply ProSpectrum.levelHom_ext
    intro i
    exact postnikovHomotopyPullbackComparison_square R n hn (f.app i).hom
  · exact fun i => postnikovClassModelComparison_quasiIso R n hn (A.obj i)
  · exact fun i => postnikovClassModelComparison_quasiIso R n hn (B.obj i)

lemma postnikovMap_reflects_cellNativeRoofProInverse_of_bounded (n : ℤ)
    (hA : ∀ i, (A.obj i).obj.X.IsGE (-n)) (hB : ∀ i, (B.obj i).obj.X.IsGE (-n))
    (hf : HasCellNativeRoofProInverse R (f.map (postnikovFunctor R n))) :
    HasCellNativeRoofProInverse R (f.map (nonpositiveInclusion R)) := by
  let a := TowerDiagram.mapNat A (postnikovQuotientNatTrans R n)
  let b := TowerDiagram.mapNat B (postnikovQuotientNatTrans R n)
  apply HasCellNativeRoofProInverse.of_square R _ _ a b ?_ ?_ ?_ hf
  · apply ProSpectrum.levelHom_ext
    intro i
    exact (postnikovQuotient_naturality R (f.app i).hom n).symm
  · exact fun i => postnikovQuotient_quasiIso R (A.obj i).obj n (hA i)
  · exact fun i => postnikovQuotient_quasiIso R (B.obj i).obj n (hB i)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
