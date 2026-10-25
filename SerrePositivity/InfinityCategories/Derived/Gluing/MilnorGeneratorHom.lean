module
public import SerrePositivity.InfinityCategories.Derived.Gluing.MilnorSquareComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.Category
public import SerrePositivity.InfinityCategories.Derived.ComplexMappingCoconeMapIso
public import SerrePositivity.KST.SConstruction.DGHomGluingActions
/-!
概要：元の自由対象の Hom gluing End 複体を、Milnor 四角形の fiber へ同定する。
方針：指定比較を単位閉元に取り、左右作用と比較差の符号を全次数で照合する。
規約：元の左右 Hom と角の Hom を使う。Perf 全対象への拡張は後続工程。
使われ方：Milnor 条件からの元対角の Hom 準同型性の自由対象での入口。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits CochainComplex HomComplex DifferentialGraded
open KST.SConstruction KST.LocalizingInvariants
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "C" => dgAlgebraCategory R d.left
local notation "D" => dgAlgebraCategory R d.right
local notation "E" => dgAlgebraCategory R d.corner
local notation "p" => dgAlgebraMap R d.lower
local notation "q" => dgAlgebraMap R d.upper
local notation "M" => dgHomGluingBimodule R (C) (D) (E) (p) (q)
abbrev DGGluingMilnorGeneratorCategory := DGGluingObject R (C) (D) (M)
def dgGluingMilnorGenerator : DGGluingMilnorGeneratorCategory R d where
  left := Opposite.op DGAlgebraPoint.star
  right := Opposite.op DGAlgebraPoint.star
  gluing := unitElement R (Opposite.op (DGAlgebraPoint.star : DGAlgebraPoint R d.corner))
local notation "X" => dgGluingMilnorGenerator R d
lemma dgGluingMilnorGenerator_leftAction :
    dgGluingLeftAction R (C) (D) (M) (X) (X) = d.lower.hom := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  rw [dgHomGluingLeftAction_apply]
  exact unit_forward R (x := Opposite.op (DGAlgebraPoint.star : DGAlgebraPoint R d.corner))
    (y := Opposite.op (DGAlgebraPoint.star : DGAlgebraPoint R d.corner)) (d.lower.hom.f n f)
lemma dgGluingMilnorGenerator_rightAction :
    dgGluingRightAction R (C) (D) (M) (X) (X) = d.upper.hom := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  rw [dgHomGluingRightAction_apply]
  exact forward_unit R (x := Opposite.op (DGAlgebraPoint.star : DGAlgebraPoint R d.corner))
    (y := Opposite.op (DGAlgebraPoint.star : DGAlgebraPoint R d.corner)) (d.upper.hom.f n f)
lemma dgGluingMilnorGenerator_difference :
    dgGluingDifference R (C) (D) (M) (X) (X) =
      -DGAlgebra.HomotopyPullbackModel.difference R d.lower d.upper := by
  rw [dgGluingDifference, dgGluingMilnorGenerator_leftAction,
    dgGluingMilnorGenerator_rightAction]
  apply biprod.hom_ext' <;>
    simp [DGAlgebra.HomotopyPullbackModel.difference, Preadditive.comp_sub]
def dgGluingMilnorCornerNegIso : d.corner.X ≅ d.corner.X where
  hom := -𝟙 _
  inv := -𝟙 _
  hom_inv_id := by simp
  inv_hom_id := by simp
def dgGluingMilnorGeneratorHomFiberIso :
    homObject R (DGGluingMilnorGeneratorCategory R d) (X) (X) ≅
      mappingCocone (DGAlgebra.HomotopyPullbackModel.difference R d.lower d.upper) :=
  complexMappingCoconeMapIso (dgGluingDifference R (C) (D) (M) (X) (X)) _
    (Iso.refl _) (dgGluingMilnorCornerNegIso R d) (by
      rw [dgGluingMilnorGenerator_difference]
      simp only [dgGluingMilnorCornerNegIso, Preadditive.comp_neg, Preadditive.neg_comp,
        neg_neg, Iso.refl_hom, Category.id_comp]
      exact Category.comp_id _)
def dgGluingMilnorGeneratorHomComparison :
    d.source.X ⟶ homObject R (DGGluingMilnorGeneratorCategory R d) (X) (X) :=
  dgGluingMilnorSquareFiberComparison R d ≫ (dgGluingMilnorGeneratorHomFiberIso R d).inv
lemma dgGluingMilnorGeneratorHomComparison_quasiIso (h : DGGluingMilnorSquare R d) :
    QuasiIso (dgGluingMilnorGeneratorHomComparison R d) := by
  let := dgGluingMilnorSquareFiberComparison_quasiIso R d h
  exact inferInstanceAs (QuasiIso (_ ≫ (dgGluingMilnorGeneratorHomFiberIso R d).inv))
end SerrePositivity.InfinityCategories
