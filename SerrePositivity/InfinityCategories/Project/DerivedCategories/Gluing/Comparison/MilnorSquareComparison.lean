module
public import SerrePositivity.KST.SConstruction.DGOdotInput
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackCoconeIso
/-!
概要：元の dg 代数四角形の Milnor 条件に使う指定比較射と、その実 fiber 表示。
方針：元の可換式の定数経路を Sp 正本の lift に渡し、既存の複体同型を合成する。
規約：比較射の準同型性だけを Milnor 仮定とする。代数模型と複体模型を区別する。
使われ方：元対角の Hom 比較と同じ二射を持つ Verdier 列の供給に用いる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits CochainComplex HomComplex DifferentialGraded
open KST.SConstruction KST.LocalizingInvariants
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
def dgGluingMilnorSquareWitness :
    DGAlgebra.Path.Witness R (d.top ≫ d.lower) (d.side ≫ d.upper) where
  hom := d.top ≫ d.lower ≫ DGAlgebra.Path.diagonal R d.corner
  source_eq := by simp only [Category.assoc, DGAlgebra.Path.diagonal_source, Category.comp_id]
  target_eq := by
    simp only [Category.assoc, DGAlgebra.Path.diagonal_target, Category.comp_id]
    exact d.commutes
def dgGluingMilnorSquareComparison :
    d.source ⟶ DGAlgebra.HomotopyPullbackModel.algebra R d.lower d.upper :=
  DGAlgebra.HomotopyPullbackModel.lift R d.lower d.upper d.top d.side
    (dgGluingMilnorSquareWitness R d)
lemma dgGluingMilnorSquareComparison_left :
    dgGluingMilnorSquareComparison R d ≫ DGAlgebra.HomotopyPullbackModel.left R d.lower d.upper =
      d.top := DGAlgebra.HomotopyPullbackModel.lift_left R _ _ _ _ _
lemma dgGluingMilnorSquareComparison_right :
    dgGluingMilnorSquareComparison R d ≫ DGAlgebra.HomotopyPullbackModel.right R d.lower d.upper =
      d.side := DGAlgebra.HomotopyPullbackModel.lift_right R _ _ _ _ _
lemma dgGluingMilnorSquareComparison_path :
    dgGluingMilnorSquareComparison R d ≫ DGAlgebra.HomotopyPullbackModel.path R d.lower d.upper =
      d.top ≫ d.lower ≫ DGAlgebra.Path.diagonal R d.corner :=
  DGAlgebra.HomotopyPullbackModel.lift_path R _ _ _ _ _
def DGGluingMilnorSquare : Prop := QuasiIso (dgGluingMilnorSquareComparison R d).hom
def dgGluingMilnorSquareFiberComparison :
    d.source.X ⟶ mappingCocone (DGAlgebra.HomotopyPullbackModel.difference R d.lower d.upper) :=
  (dgGluingMilnorSquareComparison R d).hom ≫
    (DGAlgebra.HomotopyPullbackModel.complexIso R d.lower d.upper).hom
lemma dgGluingMilnorSquareFiberComparison_left :
    dgGluingMilnorSquareFiberComparison R d ≫
      (mappingCocone.fst (DGAlgebra.HomotopyPullbackModel.difference R d.lower d.upper) ≫
        biprod.fst) = d.top.hom := by
  rw [dgGluingMilnorSquareFiberComparison, DGAlgebra.HomotopyPullbackModel.complexIso,
    Category.assoc,
    DGAlgebra.HomotopyPullbackModel.toMappingCocone_left]
  exact congrArg Mon.Hom.hom (dgGluingMilnorSquareComparison_left R d)
lemma dgGluingMilnorSquareFiberComparison_right :
    dgGluingMilnorSquareFiberComparison R d ≫
      (mappingCocone.fst (DGAlgebra.HomotopyPullbackModel.difference R d.lower d.upper) ≫
        biprod.snd) = d.side.hom := by
  rw [dgGluingMilnorSquareFiberComparison, DGAlgebra.HomotopyPullbackModel.complexIso,
    Category.assoc,
    DGAlgebra.HomotopyPullbackModel.toMappingCocone_right]
  exact congrArg Mon.Hom.hom (dgGluingMilnorSquareComparison_right R d)
lemma dgGluingMilnorSquareFiberComparison_primitive :
    (Cochain.ofHom (dgGluingMilnorSquareFiberComparison R d)).comp
      (mappingCocone.snd (DGAlgebra.HomotopyPullbackModel.difference R d.lower d.upper))
      (zero_add (-1)) = 0 := by
  rw [dgGluingMilnorSquareFiberComparison, DGAlgebra.HomotopyPullbackModel.complexIso,
    Cochain.ofHom_comp,
    Cochain.comp_assoc_of_first_is_zero_cochain,
    DGAlgebra.HomotopyPullbackModel.toMappingCocone_snd,
    DGAlgebra.HomotopyPullbackModel.primitive,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp]
  have h := congrArg Mon.Hom.hom (dgGluingMilnorSquareComparison_path R d)
  change (dgGluingMilnorSquareComparison R d).hom ≫
    (DGAlgebra.HomotopyPullbackModel.path R d.lower d.upper).hom =
      d.top.hom ≫ d.lower.hom ≫ DGAlgebra.Path.diagonalHom R d.corner at h
  rw [h, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    DGAlgebra.Path.diagonalHom_primitive, Cochain.comp_zero]
  exact Cochain.comp_zero _ _
lemma dgGluingMilnorSquareFiberComparison_quasiIso (h : DGGluingMilnorSquare R d) :
    QuasiIso (dgGluingMilnorSquareFiberComparison R d) := by
  let : QuasiIso (dgGluingMilnorSquareComparison R d).hom := h
  exact inferInstanceAs (QuasiIso (_ ≫
    (DGAlgebra.HomotopyPullbackModel.complexIso R d.lower d.upper).hom))
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
