module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.MilnorGeneratorCriterion
/-!
概要：元 Milnor 対角の自由代表の両脚と、角の同じ自由代表への閉同型を固定する。
方針：元の実延長の代表同型を、全 Hom を持つ小模型の中で保持する。
規約：対角の像を置換せず、比較先の自由 gluing 対象を別に指定する。
使われ方：自由 End の Milnor 比較を元の実対角へ輸送する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded KST.SConstruction
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
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
abbrev dgGluingMilnorFreeLeft : CL :=
  dgSmallPerfectArrowTargetRepresentable R (A) (C) (L)
    ((L).obj (dgOdotInputSourcePoint R d))
abbrev dgGluingMilnorFreeRight : DR :=
  dgSmallPerfectArrowTargetRepresentable R (A) (D) (G)
    ((G).obj (dgOdotInputSourcePoint R d))
def dgGluingMilnorDiagonalFreeLeftIso :
    ForgetEnrichment.of (Complex R)
      (((dgOdotQuotientInput R d).diagonal.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorSourceGenerator R d)).left) ≅
    ForgetEnrichment.of (Complex R) (dgGluingMilnorFreeLeft R d) := by
  let e := dgModuleExtensionRepresentableIso R (A) (C) (L) (dgOdotInputSourcePoint R d)
  exact
    { hom := e.hom
      inv := e.inv
      hom_inv_id := e.hom_inv_id
      inv_hom_id := e.inv_hom_id }
def dgGluingMilnorDiagonalFreeRightIso :
    ForgetEnrichment.of (Complex R)
      (((dgOdotQuotientInput R d).diagonal.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorSourceGenerator R d)).right) ≅
    ForgetEnrichment.of (Complex R) (dgGluingMilnorFreeRight R d) := by
  let e := dgModuleExtensionRepresentableIso R (A) (D) (G) (dgOdotInputSourcePoint R d)
  exact
    { hom := e.hom
      inv := e.inv
      hom_inv_id := e.hom_inv_id
      inv_hom_id := e.inv_hom_id }
abbrev dgGluingMilnorFreeCorner : V :=
  dgSmallPerfectEnvelopeRepresentable R (E) ((CL) ⊕ (DR))
    (dgSmallPerfectSquareCornerFamily R (A) (C) (D) (E) (L) (G) (p) (q))
    ((p).obj ((L).obj (dgOdotInputSourcePoint R d)))
def dgGluingMilnorFreeLeftCornerIso :
    ForgetEnrichment.of (Complex R) ((pS).obj (dgGluingMilnorFreeLeft R d)) ≅
      ForgetEnrichment.of (Complex R) (dgGluingMilnorFreeCorner R d) := by
  let e := dgModuleExtensionRepresentableIso R (C) (E) (p)
    ((L).obj (dgOdotInputSourcePoint R d))
  exact { hom := e.hom, inv := e.inv, hom_inv_id := e.hom_inv_id, inv_hom_id := e.inv_hom_id }
def dgGluingMilnorFreeRightCornerIso :
    ForgetEnrichment.of (Complex R) ((qS).obj (dgGluingMilnorFreeRight R d)) ≅
      ForgetEnrichment.of (Complex R) (dgGluingMilnorFreeCorner R d) := by
  let e := dgModuleExtensionRepresentableIso R (D) (E) (q)
    ((G).obj (dgOdotInputSourcePoint R d))
  exact { hom := e.hom, inv := e.inv, hom_inv_id := e.hom_inv_id, inv_hom_id := e.inv_hom_id }
def dgGluingMilnorFreeObject : DGOdotGluing R d where
  left := dgGluingMilnorFreeLeft R d
  right := dgGluingMilnorFreeRight R d
  gluing := closedHomEquiv R (V) _ _
    ((dgGluingMilnorFreeLeftCornerIso R d).hom ≫
      (dgGluingMilnorFreeRightCornerIso R d).inv)
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
