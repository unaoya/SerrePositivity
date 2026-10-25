module
public import SerrePositivity.InfinityCategories.Derived.Gluing.MilnorFreeHomComponents
public import SerrePositivity.InfinityCategories.Derived.ComplexMappingCoconeMapIso
/-!
概要：元の実自由 End と Milnor fiber の比較を、固定した三成分同型の正方形へ帰着する。
方針：同じ mapping cocone 同型で自由 Hom の準同型性を元の対角へ輸送する。
規約：残る比較差と対角作用の二等式を明示し、生成判定を追加仮定にしない。
使われ方：D-19 の代表整合を適用した後、元対角の全 Perf Hom 比較を閉じる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded KST.SConstruction
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "A" => dgAlgebraCategory R d.source
local notation "C" => dgAlgebraCategory R d.left
local notation "D" => dgAlgebraCategory R d.right
local notation "E" => dgAlgebraCategory R d.corner
local notation "L" => dgAlgebraMap R d.top
local notation "G" => dgAlgebraMap R d.side
local notation "p" => dgAlgebraMap R d.lower
local notation "q" => dgAlgebraMap R d.upper
local notation "CL" => DGSmallPerfectArrowTarget R (A) (C) (L)
local notation "DR" => DGSmallPerfectArrowTarget R (A) (D) (G)
local notation "V" => DGSmallPerfectSquareCorner R (A) (C) (D) (E) (L) (G) (p) (q)
local notation "pS" => dgSmallPerfectSquareLeftMap R (A) (C) (D) (E) (L) (G) (p) (q)
local notation "qS" => dgSmallPerfectSquareRightMap R (A) (C) (D) (E) (L) (G) (p) (q)
abbrev dgGluingMilnorActualFreeDifference :=
  dgGluingDifference R (CL) (DR) (dgHomGluingBimodule R (CL) (DR) (V) (pS) (qS))
    (dgGluingMilnorActualFreeObject R d) (dgGluingMilnorActualFreeObject R d)
abbrev dgGluingMilnorRawFreeDifference :=
  dgGluingDifference R (C) (D) (dgHomGluingBimodule R (C) (D) (E) (p) (q))
    (dgGluingMilnorGenerator R d) (dgGluingMilnorGenerator R d)
def dgGluingMilnorFreePairHomIso :=
  biprod.mapIso (dgGluingMilnorFreeLeftHomIso R d) (dgGluingMilnorFreeRightHomIso R d)
def dgGluingMilnorFreeHomIso
    (h : dgGluingMilnorActualFreeDifference R d ≫
      (dgGluingMilnorFreeCoefficientHomIso R d).hom =
      (dgGluingMilnorFreePairHomIso R d).hom ≫ dgGluingMilnorRawFreeDifference R d) :
    homObject R (DGOdotGluing R d) (dgGluingMilnorActualFreeObject R d)
      (dgGluingMilnorActualFreeObject R d) ≅
    homObject R (DGGluingMilnorGeneratorCategory R d) (dgGluingMilnorGenerator R d)
      (dgGluingMilnorGenerator R d) :=
  complexMappingCoconeMapIso _ _ (dgGluingMilnorFreePairHomIso R d)
    (dgGluingMilnorFreeCoefficientHomIso R d) h
lemma dgGluingMilnorSmallPerfectGeneration_of_freeComparison
    (hsquare : dgGluingMilnorActualFreeDifference R d ≫
      (dgGluingMilnorFreeCoefficientHomIso R d).hom =
      (dgGluingMilnorFreePairHomIso R d).hom ≫ dgGluingMilnorRawFreeDifference R d)
    (hmap : (dgOdotQuotientInput R d).diagonal.map
        (dgGluingMilnorSourceGenerator R d) (dgGluingMilnorSourceGenerator R d) ≫
        (dgGluingMilnorFreeHomIso R d hsquare).hom =
      (dgGluingMilnorFreeSourceHomIso R d).hom ≫
        (dgGluingMilnorAlgebraDiagonal R d).map
          (dgOdotInputSourcePoint R d) (dgOdotInputSourcePoint R d)) :
    DGGluingMilnorSmallPerfectGeneration R d := by
  intro hraw
  apply dgGluingMilnorSmallPerfectDiagonal_homQuasiIso_of_generator R d
  have hr := hraw (dgOdotInputSourcePoint R d) (dgOdotInputSourcePoint R d)
  letI := hr
  have hc : QuasiIso ((dgOdotQuotientInput R d).diagonal.map
      (dgGluingMilnorSourceGenerator R d) (dgGluingMilnorSourceGenerator R d) ≫
        (dgGluingMilnorFreeHomIso R d hsquare).hom) := by
    rw [hmap]
    infer_instance
  letI := hc
  exact quasiIso_of_comp_right _ (dgGluingMilnorFreeHomIso R d hsquare).hom
end SerrePositivity.InfinityCategories
