module
public import SerrePositivity.InfinityCategories.Derived.Gluing.MilnorResolvedKernel
public import SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence
/-!
概要：元の小 Perf Milnor 対角と同じ cell 平坦商の Verdier 列を構成する。
方針：対角の充満忠実性、厚い核の本質像、辺局所化を接続する。
規約：生成判定と前三角性の上流接続は明示入力であり、未分解 path 商は使わない。
使われ方：K-S• が元商射影を cell 平坦商へ付け替えるための供給。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet KST.SConstruction KST.LocalizingInvariants
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
  [IsDGPretriangulated R (DGOdotGluing R d)]
  [IsExactFunctor (dgNerve.map (dgOdotQuotientInput R d).diagonal)]
theorem dgGluingMilnor_isResolvedVerdierSequence
    (h : DGGluingMilnorSquare R d) (hgen : DGGluingMilnorSmallPerfectGeneration R d) :
    _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence (dgGluingMilnorNativeDiagonal R d)
      (dgGluingMilnorResolvedProjection R d) where
  _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence.fullyFaithful := dgGluingMilnorSmallPerfectDiagonal_isFullyFaithful R d h hgen
  _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence.kernel := dgGluingMilnorResolvedQuotient_zero_iff R d h hgen
  _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence.quotient := dgGluingMilnorResolvedQuotient_isLocalization R d h hgen
end SerrePositivity.InfinityCategories
