module

public import SerrePositivity.DifferentialGraded.Complexes.HomComplex
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
概要：実複体の二成分の直和射の恒等・合成を、元の二射影で計算する。
方針：二射影の共同単射性を使う。規約：元の直和を保持。
使われ方：底変更を含む平方零代数射の関手則。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants
variable {R : Type u} [CommRing R] {A B C D E F : Complex R}

lemma cochainBiprodMap_comp (a : A ⟶ B) (b : C ⟶ D) (c : B ⟶ E) (d : D ⟶ F) :
    biprod.map a b ≫ biprod.map c d = biprod.map (a ≫ c) (b ≫ d) := by
  apply biprod.hom_ext <;> simp [Category.assoc]

lemma cochainBiprodMap_id : biprod.map (𝟙 A) (𝟙 B) = 𝟙 (A ⊞ B) := by
  apply biprod.hom_ext <;> simp

end SerrePositivity.KST.LocalizingInvariants
