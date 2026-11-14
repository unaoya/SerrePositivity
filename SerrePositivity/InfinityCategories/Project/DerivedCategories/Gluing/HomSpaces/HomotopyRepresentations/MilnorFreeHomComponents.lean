module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.MilnorFreeLegComparison
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded KST.SConstruction
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
abbrev dgGluingMilnorActualFreeObject :=
  (dgOdotQuotientInput R d).diagonal.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorSourceGenerator R d)
local notation "A" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.source
local notation "C" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.left
local notation "D" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.right
local notation "E" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.corner
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.top
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.side
local notation "p" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.lower
local notation "q" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.upper
local notation "CL" => DGSmallPerfectArrowTarget R (A) (C) (L)
local notation "DR" => DGSmallPerfectArrowTarget R (A) (D) (G)
local notation "V" => DGSmallPerfectSquareCorner R (A) (C) (D) (E) (L) (G) (p) (q)
local notation "pS" => dgSmallPerfectSquareLeftMap R (A) (C) (D) (E) (L) (G) (p) (q)
local notation "qS" => dgSmallPerfectSquareRightMap R (A) (C) (D) (E) (L) (G) (p) (q)
def dgGluingMilnorFreeSourceHomIso :
    homObject R (DGSmallPerfectBase R (A)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorSourceGenerator R d)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorSourceGenerator R d) ≅
    homObject R (A) (dgOdotInputSourcePoint R d) (dgOdotInputSourcePoint R d) :=
  dgYonedaIso R (dgOdotInputSourcePoint R d)
    (representable R (dgOdotInputSourcePoint R d))
def dgGluingMilnorFreeLeftHomIso :
    homObject R (CL) (dgGluingMilnorActualFreeObject R d).left
      (dgGluingMilnorActualFreeObject R d).left ≅
    homObject R (C) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorGenerator R d).left (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorGenerator R d).left :=
  enrichedClosedIsoHomIso (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorDiagonalFreeLeftIso R d)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorDiagonalFreeLeftIso R d) ≪≫
  dgYonedaIso R ((L).obj (dgOdotInputSourcePoint R d))
    (representable R ((L).obj (dgOdotInputSourcePoint R d)))
def dgGluingMilnorFreeRightHomIso :
    homObject R (DR) (dgGluingMilnorActualFreeObject R d).right
      (dgGluingMilnorActualFreeObject R d).right ≅
    homObject R (D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorGenerator R d).right (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorGenerator R d).right :=
  enrichedClosedIsoHomIso (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorDiagonalFreeRightIso R d)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorDiagonalFreeRightIso R d) ≪≫
  dgYonedaIso R ((G).obj (dgOdotInputSourcePoint R d))
    (representable R ((G).obj (dgOdotInputSourcePoint R d)))
def dgGluingMilnorActualFreeLeftCornerIso :
    ForgetEnrichment.of (Complex R) ((pS).obj (dgGluingMilnorActualFreeObject R d).left) ≅
      ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeCorner R d) :=
  (pS).onClosed.mapIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorDiagonalFreeLeftIso R d) ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeLeftCornerIso R d
def dgGluingMilnorActualFreeRightCornerIso :
    ForgetEnrichment.of (Complex R) ((qS).obj (dgGluingMilnorActualFreeObject R d).right) ≅
      ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeCorner R d) :=
  (qS).onClosed.mapIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorDiagonalFreeRightIso R d) ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeRightCornerIso R d
def dgGluingMilnorFreeCoefficientHomIso :
    (dgHomGluingBimodule R (CL) (DR) (V) (pS) (qS)).value
      (dgGluingMilnorActualFreeObject R d).left (dgGluingMilnorActualFreeObject R d).right ≅
    (dgHomGluingBimodule R (C) (D) (E) (p) (q)).value
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorGenerator R d).left (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorGenerator R d).right :=
  enrichedClosedIsoHomIso (Complex R) (dgGluingMilnorActualFreeLeftCornerIso R d)
    (dgGluingMilnorActualFreeRightCornerIso R d) ≪≫
  dgYonedaIso R ((p).obj ((L).obj (dgOdotInputSourcePoint R d)))
    (representable R ((p).obj ((L).obj (dgOdotInputSourcePoint R d))))
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
