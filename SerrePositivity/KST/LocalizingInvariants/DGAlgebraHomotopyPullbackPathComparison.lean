module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathCospanComparison
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackMapQuasiIso
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackSourceQuasiIso

/-!
概要：実経路で可換な classifying cospan を、元の経路模型の実準同型 zigzag で比較。
方針：mapping-path による二つの厳密化と、元の源の比較の三つの実射を構成する。
規約：三射とも元の右脚を保持。最後の準同型性は源の比較の準同型性の下。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PathCospanComparison
variable (R : Type u) [CommRing R] {A B C W : Mon (Complex R)} (f : A ⟶ B) (g : C ⟶ B)
  (a : W ⟶ B) (q : W ⟶ A) (h : Path.Witness R a (q ≫ f))

def originalToPath : HomotopyPullbackModel.algebra R a g ⟶
    HomotopyPullbackModel.algebra R (MappingPath.target R a) g :=
  HomotopyPullbackModel.map R a g _ g (MappingPath.section_ R a) (𝟙 B) (𝟙 C)
    (by rw [MappingPath.section_target, Category.comp_id]) (by simp)

def composedToPath : HomotopyPullbackModel.algebra R (q ≫ f) g ⟶
    HomotopyPullbackModel.algebra R (MappingPath.target R a) g :=
  HomotopyPullbackModel.map R (q ≫ f) g _ g (witnessMap R f a q h) (𝟙 B) (𝟙 C)
    (by rw [witnessMap_target, Category.comp_id]) (by simp)

def composedToOriginal : HomotopyPullbackModel.algebra R (q ≫ f) g ⟶
    HomotopyPullbackModel.algebra R f g := HomotopyPullbackModel.sourceMap R f g q

lemma originalToPath_quasiIso : QuasiIso (originalToPath R g a).hom :=
  HomotopyPullbackModel.map_quasiIso R _ _ _ _ _ _ _ _ _
    (MappingPath.section_quasiIso R a) (quasiIso_of_isIso _) (quasiIso_of_isIso _)

lemma composedToPath_quasiIso : QuasiIso (composedToPath R f g a q h).hom :=
  HomotopyPullbackModel.map_quasiIso R _ _ _ _ _ _ _ _ _
    (witnessMap_quasiIso R f a q h) (quasiIso_of_isIso _) (quasiIso_of_isIso _)

lemma composedToOriginal_quasiIso (hq : QuasiIso q.hom) :
    QuasiIso (composedToOriginal R f g q).hom :=
  HomotopyPullbackModel.sourceMap_quasiIso R f g q hq

lemma originalToPath_right : originalToPath R g a ≫ HomotopyPullbackModel.right R _ _ =
    HomotopyPullbackModel.right R _ _ :=
  (HomotopyPullbackModel.map_right R _ _ _ _ _ _ _ _ _).trans (Category.comp_id _)

lemma composedToPath_right : composedToPath R f g a q h ≫ HomotopyPullbackModel.right R _ _ =
    HomotopyPullbackModel.right R _ _ :=
  (HomotopyPullbackModel.map_right R _ _ _ _ _ _ _ _ _).trans (Category.comp_id _)

lemma composedToOriginal_right : composedToOriginal R f g q ≫
    HomotopyPullbackModel.right R _ _ = HomotopyPullbackModel.right R _ _ :=
  HomotopyPullbackModel.sourceMap_right R _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PathCospanComparison
