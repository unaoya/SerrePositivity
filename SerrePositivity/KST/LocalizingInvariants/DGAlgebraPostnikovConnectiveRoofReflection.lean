module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConnectiveProRoofSquare
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovClassConnectiveProReflection

/-!
概要：class 比較と有界商射で、connective 準同型反転での実 roof の逆を反映する。
方針：元の自然性の正方形と比較の MappingPath 逆を用い、同じ span を各関手で評価。
規約：局所化の等式から実経路を仮定しない。使われ方：元の一切断射への roof 抽出。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {D : Type v} [Category.{w} D]

lemma postnikovClassModelMap_reflects_connectiveRoofProInverse (n : ℤ) (hn : 0 ≤ n)
    (hf : HasConnectiveRoofProInverse R (D := D)
      (f.map (postnikovClassModelFunctor R n hn))
      (fun i => postnikovClassModel_isConnective R (B.obj i).obj n hn)) :
    HasConnectiveRoofProInverse R (D := D) (f.map (postnikovFunctor R (n + 1)))
      (fun i => postnikov_isConnective R (B.obj i).obj (n + 1)) := by
  let a := TowerDiagram.mapNat A (postnikovClassModelComparison R n hn)
  let b := TowerDiagram.mapNat B (postnikovClassModelComparison R n hn)
  apply HasConnectiveRoofProInverse.of_square R _ _ a b ?_ ?_ ?_
    (fun i => postnikov_isConnective R (B.obj i).obj (n + 1))
    (fun i => postnikovClassModel_isConnective R (A.obj i).obj n hn)
    (fun i => postnikovClassModel_isConnective R (B.obj i).obj n hn) hf
  · apply ProSpectrum.levelHom_ext
    intro i
    exact postnikovHomotopyPullbackComparison_square R n hn (f.app i).hom
  · exact fun i => postnikovClassModelComparison_quasiIso R n hn (A.obj i)
  · exact fun i => postnikovClassModelComparison_quasiIso R n hn (B.obj i)

lemma postnikovMap_reflects_connectiveRoofProInverse_of_bounded (n : ℤ)
    (hA : ∀ i, (A.obj i).obj.X.IsGE (-n)) (hB : ∀ i, (B.obj i).obj.X.IsGE (-n))
    (hf : HasConnectiveRoofProInverse R (D := D) (f.map (postnikovFunctor R n))
      (fun i => postnikov_isConnective R (B.obj i).obj n)) :
    HasConnectiveRoofProInverse R (D := D) (f.map (nonpositiveInclusion R))
      (fun i => nonpositive_isConnective R (B.obj i).obj) := by
  let a := TowerDiagram.mapNat A (postnikovQuotientNatTrans R n)
  let b := TowerDiagram.mapNat B (postnikovQuotientNatTrans R n)
  apply HasConnectiveRoofProInverse.of_square R _ _ a b ?_ ?_ ?_
    (fun i => nonpositive_isConnective R (B.obj i).obj)
    (fun i => postnikov_isConnective R (A.obj i).obj n)
    (fun i => postnikov_isConnective R (B.obj i).obj n) hf
  · apply ProSpectrum.levelHom_ext
    intro i
    exact (postnikovQuotient_naturality R (f.app i).hom n).symm
  · exact fun i => postnikovQuotient_quasiIso R (A.obj i).obj n (hA i)
  · exact fun i => postnikovQuotient_quasiIso R (B.obj i).obj n (hB i)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
