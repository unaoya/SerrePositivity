module
public import SerrePositivity.InfinityCategories.Derived.Gluing.MilnorFreeDifferenceSquare
public import SerrePositivity.InfinityCategories.Derived.Gluing.MilnorNativePretriangulated
/-!
概要：dg Milnor 四角形から元小 Perf 対角と cell 平坦商の Verdier 列を供給する。
方針：自由 End の厳密比較と生成判定を、同じ実 thick 核・局所化へ接続する。
規約：仮定は正本 Milnor 比較の準同型性のみとし、元対角と実商射影を保持する。
使われ方：K-S• が元射影を resolved 商へ付け替える際の公開入口。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet KST.SConstruction KST.LocalizingInvariants
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
lemma dgGluingMilnorSmallPerfectDiagonal_homQuasiIso_of_milnor
    (h : DGGluingMilnorSquare R d) :
    HomQuasiIso (dgOdotQuotientInput R d).diagonal :=
  dgGluingMilnorSmallPerfectDiagonal_homQuasiIso R d h
    (dgGluingMilnorSmallPerfectGeneration R d)
lemma dgGluingMilnorSmallPerfectDiagonal_isFullyFaithful_of_milnor
    (h : DGGluingMilnorSquare R d) :
    IsFullyFaithful (dgNerve.map (dgOdotQuotientInput R d).diagonal) :=
  dgGluingMilnorSmallPerfectDiagonal_isFullyFaithful R d h
    (dgGluingMilnorSmallPerfectGeneration R d)
lemma dgGluingMilnorDiagonalExactMap_isFullyFaithful_of_milnor
    (h : DGGluingMilnorSquare R d) :
    IsFullyFaithful (dgOdotDiagonalExactMap R d).hom :=
  dgGluingMilnorDiagonalExactMap_isFullyFaithful R d h
    (dgGluingMilnorSmallPerfectGeneration R d)
local instance : IsDGPretriangulated R (DGOdotGluing R d) :=
  dgGluingMilnor_isDGPretriangulated R d
local instance : IsExactFunctor (dgNerve.map (dgOdotQuotientInput R d).diagonal) :=
  dgGluingMilnorNativeDiagonal_isExactFunctor R d
theorem dgGluingMilnor_isResolvedVerdierSequence_of_milnor
    (h : DGGluingMilnorSquare R d) :
    IsVerdierSequence (dgGluingMilnorNativeDiagonal R d)
      (dgGluingMilnorResolvedProjection R d) :=
  dgGluingMilnor_isResolvedVerdierSequence_of_generation R d h
    (dgGluingMilnorSmallPerfectGeneration R d)
end SerrePositivity.InfinityCategories
