module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackPathComparison

/-!
概要：元の実経路で結ばれた二つの底射の経路模型を、同じ実準同型模型へ結ぶ。
方針：既存の mapping-path による厳密化と、元の指定経路の実 lift を使う。
規約：底射や右脚の準同型性は不要。使われ方：roof の右経路に沿う底変更比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PathBaseChange
variable (R : Type u) [CommRing R] {P B U : Mon (Complex R)}
  (a b : P ⟶ B) (q : U ⟶ B) (w : Path.Witness R a b)

def identityWitness : Path.Witness R a ((𝟙 P) ≫ b) where
  hom := w.hom
  source_eq := w.source_eq
  target_eq := w.target_eq.trans (Category.id_comp b).symm

def changeMap : P ⟶ MappingPath.algebra R a :=
  PathCospanComparison.witnessMap R b a (𝟙 P) (identityWitness R a b w)

lemma changeMap_target : changeMap R a b w ≫ MappingPath.target R a = b := by
  exact (PathCospanComparison.witnessMap_target R b a (𝟙 P) (identityWitness R a b w)).trans
    (Category.id_comp b)

lemma changeMap_projection : changeMap R a b w ≫ MappingPath.projection R a = 𝟙 P :=
  PathCospanComparison.witnessMap_projection R b a (𝟙 P) (identityWitness R a b w)

lemma changeMap_inclusion : changeMap R a b w ≫ MappingPath.inclusion R a = w.hom :=
  MappingPath.lift_inclusion R a (identityWitness R a b w).hom (𝟙 P)
    (by rw [(identityWitness R a b w).source_eq, Category.id_comp])

lemma changeMap_quasiIso : QuasiIso (changeMap R a b w).hom :=
  PathCospanComparison.witnessMap_quasiIso R b a (𝟙 P) (identityWitness R a b w)

def common : Mon (Complex R) := HomotopyPullbackModel.algebra R (MappingPath.target R a) q

def first : HomotopyPullbackModel.algebra R a q ⟶ common R a q :=
  PathCospanComparison.originalToPath R q a

def second : HomotopyPullbackModel.algebra R b q ⟶ common R a q :=
  HomotopyPullbackModel.map R b q (MappingPath.target R a) q (changeMap R a b w) (𝟙 B) (𝟙 U)
    ((changeMap_target R a b w).trans (Category.comp_id b).symm) (by simp)

lemma first_quasiIso : QuasiIso (first R a q).hom :=
  PathCospanComparison.originalToPath_quasiIso R q a

lemma second_quasiIso : QuasiIso (second R a b q w).hom :=
  HomotopyPullbackModel.map_quasiIso R _ _ _ _ _ _ _ _ _
    (changeMap_quasiIso R a b w) (quasiIso_of_isIso _) (quasiIso_of_isIso _)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PathBaseChange
