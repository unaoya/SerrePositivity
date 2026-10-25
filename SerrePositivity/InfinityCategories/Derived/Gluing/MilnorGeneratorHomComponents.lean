module
public import SerrePositivity.InfinityCategories.Derived.Gluing.MilnorGeneratorHom
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits CochainComplex HomComplex DifferentialGraded
open KST.SConstruction KST.LocalizingInvariants
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "C" => dgAlgebraCategory R d.left
local notation "D" => dgAlgebraCategory R d.right
local notation "E" => dgAlgebraCategory R d.corner
local notation "M" => dgHomGluingBimodule R (C) (D) (E)
  (dgAlgebraMap R d.lower) (dgAlgebraMap R d.upper)
local notation "X" => dgGluingMilnorGenerator R d
local notation "a" => dgGluingDifference R (C) (D) (M) (X) (X)
local notation "b" => DGAlgebra.HomotopyPullbackModel.difference R d.lower d.upper
lemma dgGluingMilnorGeneratorHomFiberIso_inv_fst :
    (dgGluingMilnorGeneratorHomFiberIso R d).inv ≫ mappingCocone.fst (a) =
      mappingCocone.fst (b) := by
  dsimp only [dgGluingMilnorGeneratorHomFiberIso, complexMappingCoconeMapIso]
  rw [complexMappingCoconeMap_fst]
  exact Category.comp_id _
lemma dgGluingMilnorGeneratorHomFiberIso_inv_primitive :
    (Cochain.ofHom (dgGluingMilnorGeneratorHomFiberIso R d).inv).comp
      (mappingCocone.snd (a)) (zero_add (-1)) =
    (mappingCocone.snd (b)).comp (Cochain.ofHom (-𝟙 d.corner.X)) (add_zero (-1)) := by
  dsimp only [dgGluingMilnorGeneratorHomFiberIso, complexMappingCoconeMapIso]
  rw [complexMappingCoconeMap_snd]
  rfl
lemma dgGluingMilnorGeneratorHomComparison_left :
    dgGluingMilnorGeneratorHomComparison R d ≫
      (mappingCocone.fst (a) ≫ biprod.fst) = d.top.hom := by
  rw [dgGluingMilnorGeneratorHomComparison, ← Category.assoc,
    Category.assoc (dgGluingMilnorSquareFiberComparison R d),
    dgGluingMilnorGeneratorHomFiberIso_inv_fst, Category.assoc]
  exact dgGluingMilnorSquareFiberComparison_left R d
lemma dgGluingMilnorGeneratorHomComparison_right :
    dgGluingMilnorGeneratorHomComparison R d ≫
      (mappingCocone.fst (a) ≫ biprod.snd) = d.side.hom := by
  rw [dgGluingMilnorGeneratorHomComparison, ← Category.assoc,
    Category.assoc (dgGluingMilnorSquareFiberComparison R d),
    dgGluingMilnorGeneratorHomFiberIso_inv_fst, Category.assoc]
  exact dgGluingMilnorSquareFiberComparison_right R d
lemma dgGluingMilnorGeneratorHomComparison_primitive :
    (Cochain.ofHom (dgGluingMilnorGeneratorHomComparison R d)).comp
      (mappingCocone.snd (a)) (zero_add (-1)) = 0 := by
  rw [dgGluingMilnorGeneratorHomComparison, Cochain.ofHom_comp,
    Cochain.comp_assoc_of_first_is_zero_cochain,
    dgGluingMilnorGeneratorHomFiberIso_inv_primitive,
    ← Cochain.comp_assoc_of_first_is_zero_cochain,
    dgGluingMilnorSquareFiberComparison_primitive, Cochain.zero_comp]
end SerrePositivity.InfinityCategories
