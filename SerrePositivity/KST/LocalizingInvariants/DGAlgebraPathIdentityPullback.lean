module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackLift

/-!
概要：経路代数を恒等二脚の homotopy pullback 模型と、全経路を保つ実代数同型で結ぶ。
方針：経路の両評価と恒等経路を普遍 lift に渡し、三成分の一意性を使う。
規約：両端だけで同型を判定しない。使われ方：端点と指定底経路を保つ cell 持ち上げ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
variable (R : Type u) [CommRing R] (C : Mon (Complex R))

def identityPullbackWitness : Witness R (source R C ≫ 𝟙 C) (target R C ≫ 𝟙 C) where
  hom := 𝟙 (algebra R C)
  source_eq := by simp
  target_eq := by simp

def toIdentityPullback : algebra R C ⟶ HomotopyPullbackModel.algebra R (𝟙 C) (𝟙 C) :=
  HomotopyPullbackModel.lift R (𝟙 C) (𝟙 C) (source R C) (target R C)
    (identityPullbackWitness R C)

lemma toIdentityPullback_left : toIdentityPullback R C ≫
    HomotopyPullbackModel.left R (𝟙 C) (𝟙 C) = source R C :=
  HomotopyPullbackModel.lift_left R _ _ _ _ _

lemma toIdentityPullback_right : toIdentityPullback R C ≫
    HomotopyPullbackModel.right R (𝟙 C) (𝟙 C) = target R C :=
  HomotopyPullbackModel.lift_right R _ _ _ _ _

lemma toIdentityPullback_path : toIdentityPullback R C ≫
    HomotopyPullbackModel.path R (𝟙 C) (𝟙 C) = 𝟙 (algebra R C) :=
  HomotopyPullbackModel.lift_path R _ _ _ _ _

def identityPullbackIso : algebra R C ≅ HomotopyPullbackModel.algebra R (𝟙 C) (𝟙 C) where
  hom := toIdentityPullback R C
  inv := HomotopyPullbackModel.path R (𝟙 C) (𝟙 C)
  hom_inv_id := toIdentityPullback_path R C
  inv_hom_id := by
    apply HomotopyPullbackModel.hom_ext R (𝟙 C) (𝟙 C)
    · rw [Category.assoc, toIdentityPullback_left, HomotopyPullbackModel.path_source,
        Category.comp_id, Category.id_comp]
    · rw [Category.assoc, toIdentityPullback_right, HomotopyPullbackModel.path_target,
        Category.comp_id, Category.id_comp]
    · rw [Category.assoc, toIdentityPullback_path, Category.comp_id, Category.id_comp]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
