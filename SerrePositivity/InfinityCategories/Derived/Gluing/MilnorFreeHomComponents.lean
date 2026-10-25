module
public import SerrePositivity.InfinityCategories.Derived.Gluing.MilnorFreeLegComparison
/-!
概要：元対角の実自由 End の三成分を、元の代数 Hom 複体へ同型で戻す。
方針：閉零の代表同型による全 Hom 共役と、同じ Yoneda 評価同型を合成する。
規約：元の実自由対象を保ち、比較差の可換性は別に検証する。
使われ方：実自由 End と Milnor fiber の mapping cocone 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded KST.SConstruction
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
abbrev dgGluingMilnorActualFreeObject :=
  (dgOdotQuotientInput R d).diagonal.obj (dgGluingMilnorSourceGenerator R d)
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
def dgGluingMilnorFreeSourceHomIso :
    homObject R (DGSmallPerfectBase R (A)) (dgGluingMilnorSourceGenerator R d)
      (dgGluingMilnorSourceGenerator R d) ≅
    homObject R (A) (dgOdotInputSourcePoint R d) (dgOdotInputSourcePoint R d) :=
  dgYonedaIso R (dgOdotInputSourcePoint R d)
    (representable R (dgOdotInputSourcePoint R d))
def dgGluingMilnorFreeLeftHomIso :
    homObject R (CL) (dgGluingMilnorActualFreeObject R d).left
      (dgGluingMilnorActualFreeObject R d).left ≅
    homObject R (C) (dgGluingMilnorGenerator R d).left (dgGluingMilnorGenerator R d).left :=
  enrichedClosedIsoHomIso (Complex R) (dgGluingMilnorDiagonalFreeLeftIso R d)
    (dgGluingMilnorDiagonalFreeLeftIso R d) ≪≫
  dgYonedaIso R ((L).obj (dgOdotInputSourcePoint R d))
    (representable R ((L).obj (dgOdotInputSourcePoint R d)))
def dgGluingMilnorFreeRightHomIso :
    homObject R (DR) (dgGluingMilnorActualFreeObject R d).right
      (dgGluingMilnorActualFreeObject R d).right ≅
    homObject R (D) (dgGluingMilnorGenerator R d).right (dgGluingMilnorGenerator R d).right :=
  enrichedClosedIsoHomIso (Complex R) (dgGluingMilnorDiagonalFreeRightIso R d)
    (dgGluingMilnorDiagonalFreeRightIso R d) ≪≫
  dgYonedaIso R ((G).obj (dgOdotInputSourcePoint R d))
    (representable R ((G).obj (dgOdotInputSourcePoint R d)))
def dgGluingMilnorActualFreeLeftCornerIso :
    ForgetEnrichment.of (Complex R) ((pS).obj (dgGluingMilnorActualFreeObject R d).left) ≅
      ForgetEnrichment.of (Complex R) (dgGluingMilnorFreeCorner R d) :=
  (pS).onClosed.mapIso (dgGluingMilnorDiagonalFreeLeftIso R d) ≪≫
    dgGluingMilnorFreeLeftCornerIso R d
def dgGluingMilnorActualFreeRightCornerIso :
    ForgetEnrichment.of (Complex R) ((qS).obj (dgGluingMilnorActualFreeObject R d).right) ≅
      ForgetEnrichment.of (Complex R) (dgGluingMilnorFreeCorner R d) :=
  (qS).onClosed.mapIso (dgGluingMilnorDiagonalFreeRightIso R d) ≪≫
    dgGluingMilnorFreeRightCornerIso R d
def dgGluingMilnorFreeCoefficientHomIso :
    (dgHomGluingBimodule R (CL) (DR) (V) (pS) (qS)).value
      (dgGluingMilnorActualFreeObject R d).left (dgGluingMilnorActualFreeObject R d).right ≅
    (dgHomGluingBimodule R (C) (D) (E) (p) (q)).value
      (dgGluingMilnorGenerator R d).left (dgGluingMilnorGenerator R d).right :=
  enrichedClosedIsoHomIso (Complex R) (dgGluingMilnorActualFreeLeftCornerIso R d)
    (dgGluingMilnorActualFreeRightCornerIso R d) ≪≫
  dgYonedaIso R ((p).obj ((L).obj (dgOdotInputSourcePoint R d)))
    (representable R ((p).obj ((L).obj (dgOdotInputSourcePoint R d))))
end SerrePositivity.InfinityCategories
