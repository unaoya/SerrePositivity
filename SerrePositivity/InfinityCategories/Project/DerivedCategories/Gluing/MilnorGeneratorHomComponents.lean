module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.MilnorGeneratorHom
/-!
概要：Milnor 自由対象の Hom 比較は元の二射と零比較 cochain を保持する。
方針：符号を変える cocone 同型の逆射の全成分を回収する。
規約：比較差 gμ−νf と Sp 正本の差の反転を明示する。
使われ方：元の厳密対角の Hom 作用との一意性による照合に用いる。
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
local notation "C" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.left
local notation "D" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.right
local notation "E" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.corner
local notation "M" => dgHomGluingBimodule R (C) (D) (E)
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.lower) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.upper)
local notation "X" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorGenerator R d
local notation "a" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R (C) (D) (M) (X) (X)
local notation "b" => DGAlgebra.HomotopyPullbackModel.difference R d.lower d.upper
lemma dgGluingMilnorGeneratorHomFiberIso_inv_fst :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorGeneratorHomFiberIso R d).inv ≫ mappingCocone.fst (a) =
      mappingCocone.fst (b) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorGeneratorHomFiberIso, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMapIso]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_fst]
  exact Category.comp_id _
lemma dgGluingMilnorGeneratorHomFiberIso_inv_primitive :
    (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorGeneratorHomFiberIso R d).inv).comp
      (mappingCocone.snd (a)) (zero_add (-1)) =
    (mappingCocone.snd (b)).comp (Cochain.ofHom (-𝟙 d.corner.X)) (add_zero (-1)) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorGeneratorHomFiberIso, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMapIso]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_snd]
  rfl
lemma dgGluingMilnorGeneratorHomComparison_left :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorGeneratorHomComparison R d ≫
      (mappingCocone.fst (a) ≫ biprod.fst) = d.top.hom := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorGeneratorHomComparison, ← Category.assoc,
    Category.assoc (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorSquareFiberComparison R d),
    dgGluingMilnorGeneratorHomFiberIso_inv_fst, Category.assoc]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorSquareFiberComparison_left R d
lemma dgGluingMilnorGeneratorHomComparison_right :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorGeneratorHomComparison R d ≫
      (mappingCocone.fst (a) ≫ biprod.snd) = d.side.hom := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorGeneratorHomComparison, ← Category.assoc,
    Category.assoc (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorSquareFiberComparison R d),
    dgGluingMilnorGeneratorHomFiberIso_inv_fst, Category.assoc]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorSquareFiberComparison_right R d
lemma dgGluingMilnorGeneratorHomComparison_primitive :
    (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorGeneratorHomComparison R d)).comp
      (mappingCocone.snd (a)) (zero_add (-1)) = 0 := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorGeneratorHomComparison, Cochain.ofHom_comp,
    Cochain.comp_assoc_of_first_is_zero_cochain,
    dgGluingMilnorGeneratorHomFiberIso_inv_primitive,
    ← Cochain.comp_assoc_of_first_is_zero_cochain,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorSquareFiberComparison_primitive, Cochain.zero_comp]
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
