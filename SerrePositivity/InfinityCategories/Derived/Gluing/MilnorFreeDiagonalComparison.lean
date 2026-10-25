module
public import SerrePositivity.InfinityCategories.Derived.Gluing.MilnorFreeHomTransportComponents
public import SerrePositivity.InfinityCategories.Derived.Gluing.MilnorActualDiagonalHomComponents
public import SerrePositivity.InfinityCategories.Derived.Gluing.MilnorFreeLeftHomAction
public import SerrePositivity.InfinityCategories.Derived.Gluing.MilnorFreeRightHomAction
/-!
概要：元の実自由対角作用を、三成分を保持する Milnor Hom 比較へ照合する。
方針：左右の代数射への評価と零比較を三成分一意性へ渡す。
規約：比較差の正方形は明示し、元の対角作用そのものを使う。
使われ方：D-19 の整合式から元対角の全 Hom 準同型性へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits CochainComplex HomComplex DifferentialGraded KST.SConstruction
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
local notation "M" => dgHomGluingBimodule R (CL) (DR) (V) (pS) (qS)
local notation "N" => dgHomGluingBimodule R (C) (D) (E) (p) (q)
local notation "X" => dgGluingMilnorActualFreeObject R d
local notation "Y" => dgGluingMilnorGenerator R d
variable (h : dgGluingMilnorActualFreeDifference R d ≫
    (dgGluingMilnorFreeCoefficientHomIso R d).hom =
    (dgGluingMilnorFreePairHomIso R d).hom ≫ dgGluingMilnorRawFreeDifference R d)
lemma dgGluingMilnorFreeDiagonal_map :
    (dgOdotQuotientInput R d).diagonal.map
        (dgGluingMilnorSourceGenerator R d) (dgGluingMilnorSourceGenerator R d) ≫
        (dgGluingMilnorFreeHomIso R d h).hom =
      (dgGluingMilnorFreeSourceHomIso R d).hom ≫
        (dgGluingMilnorAlgebraDiagonal R d).map
          (dgOdotInputSourcePoint R d) (dgOdotInputSourcePoint R d) := by
  apply dgGluingHom_ext R (C) (D) (N) (Y) (Y)
    (homObject R (DGSmallPerfectBase R (A))
      (dgGluingMilnorSourceGenerator R d) (dgGluingMilnorSourceGenerator R d))
  · rw [Category.assoc, dgGluingMilnorFreeHomIso_left, ← Category.assoc,
      dgGluingMilnorActualDiagonal_map_left, dgGluingMilnorFreeLeftHomMap_evaluate,
      Category.assoc, dgGluingMilnorAlgebraDiagonal_map_left]
    rfl
  · rw [Category.assoc, dgGluingMilnorFreeHomIso_right, ← Category.assoc,
      dgGluingMilnorActualDiagonal_map_right, dgGluingMilnorFreeRightHomMap_evaluate,
      Category.assoc, dgGluingMilnorAlgebraDiagonal_map_right]
    rfl
  · rw [dgGluingMilnorFreeHomIso_comparison,
      dgGluingMilnorActualDiagonal_map_comparison, Cochain.zero_comp]
    have hr := dgGluingMilnorAlgebraDiagonal_map_comparison R d
      (dgOdotInputSourcePoint R d) (dgOdotInputSourcePoint R d)
    apply Cochain.ext
    intro i j hij
    have he := congrArg (fun t => (dgGluingMilnorFreeSourceHomIso R d).hom.f i ≫
      t.v i j hij) hr
    simpa only [dgGluingHomComparison, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
      HomologicalComplex.comp_f, Cochain.zero_v, comp_zero, Category.assoc] using he.symm
include h in
lemma dgGluingMilnorSmallPerfectGeneration_of_freeSquare :
    DGGluingMilnorSmallPerfectGeneration R d :=
  dgGluingMilnorSmallPerfectGeneration_of_freeComparison R d h
    (dgGluingMilnorFreeDiagonal_map R d h)
end SerrePositivity.InfinityCategories
