module
public import SerrePositivity.DifferentialGraded.Verdier.Kernel

/-! # U16b からの指定局所 Morita 比較の公理監査 -/
@[expose] public section
noncomputable section
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGQuotient
#print axioms graphPairKernelColumnsPerfect
#print axioms graphPairKernelPerfectIsEquivalence
#print axioms graphPairKernelSupportedColumns
#print axioms graphPairLocalMoritaEquivalence
#print axioms graphPairLocalMoritaIsTriangulated
#print axioms graphPairLocalMoritaSquareCommShift
#print axioms graphPairLocalMoritaSquareTriangle

/-- 全対象を指定する例では、零部分圏の反映条件は元の Perf の所属証拠で満たせる。 -/
example (A : Type) [CommRing A] (D E : Type) [DGCategory A D] [DGCategory A E]
    [Small.{0} D] [Small.{0} E] (F : DGFunctor A D E) (hF : QuasiEquivalence F)
    (hD : localKFlat A D Set.univ) (hE : localKFlat A E Set.univ) :
    PerfectDGHomotopyCategoryOver A (QuotientObject D Set.univ) Set.univ ≌
      PerfectDGHomotopyCategoryOver A (QuotientObject E Set.univ) Set.univ :=
  graphPairLocalMoritaEquivalence A D E F Set.univ Set.univ (fun _ _ => Set.mem_univ _)
    hF (fun X _ => X.property) hD hE
