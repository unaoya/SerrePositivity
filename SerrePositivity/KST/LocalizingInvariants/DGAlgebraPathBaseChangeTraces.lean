module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathBaseChangeCommon

/-!
概要：共通の経路模型への両比較は、元の底・上段と指定した実底経路を保持する。
方針：元の mapping-path 射影・包含を通して両比較の実三成分を計算する。
規約：両端だけの同定で済ませない。使われ方：元の roof の右三角形の保持。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PathBaseChange
variable (R : Type u) [CommRing R] {P B U : Mon (Complex R)}
  (a b : P ⟶ B) (q : U ⟶ B) (w : Path.Witness R a b)

def base : common R a q ⟶ P :=
  HomotopyPullbackModel.left R (MappingPath.target R a) q ≫ MappingPath.projection R a

def upper : common R a q ⟶ U := HomotopyPullbackModel.right R (MappingPath.target R a) q

def trace : common R a q ⟶ Path.algebra R B :=
  HomotopyPullbackModel.left R (MappingPath.target R a) q ≫ MappingPath.inclusion R a

lemma first_base : first R a q ≫ base R a q = HomotopyPullbackModel.left R a q := by
  rw [first, PathCospanComparison.originalToPath, base, ← Category.assoc,
    HomotopyPullbackModel.map_left, Category.assoc,
    MappingPath.section_projection, Category.comp_id]

lemma second_base : second R a b q w ≫ base R a q = HomotopyPullbackModel.left R b q := by
  rw [second, base, ← Category.assoc, HomotopyPullbackModel.map_left, Category.assoc,
    changeMap_projection, Category.comp_id]

lemma first_upper : first R a q ≫ upper R a q = HomotopyPullbackModel.right R a q :=
  PathCospanComparison.originalToPath_right R q a

lemma second_upper : second R a b q w ≫ upper R a q = HomotopyPullbackModel.right R b q := by
  exact (HomotopyPullbackModel.map_right R _ _ _ _ _ _ _ _ _).trans (Category.comp_id _)

lemma first_trace : first R a q ≫ trace R a q =
    HomotopyPullbackModel.left R a q ≫ a ≫ Path.diagonal R B := by
  rw [first, PathCospanComparison.originalToPath, trace, ← Category.assoc,
    HomotopyPullbackModel.map_left, Category.assoc,
    MappingPath.section_inclusion]

lemma second_trace : second R a b q w ≫ trace R a q =
    HomotopyPullbackModel.left R b q ≫ w.hom := by
  rw [second, trace, ← Category.assoc, HomotopyPullbackModel.map_left, Category.assoc,
    changeMap_inclusion]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PathBaseChange
