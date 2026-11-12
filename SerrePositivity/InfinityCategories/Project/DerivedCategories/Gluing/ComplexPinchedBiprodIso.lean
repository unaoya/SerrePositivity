module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ComplexPinchedBiprodPullback
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-! 元の直和複体の実空間模型は、両射影を保って元の二つの空間の直積と厳密に同型。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory DifferentialGraded
variable {R : Type u} [CommRing R] (P Q : Complex R)

def dgGluingComplexPinchedBiprodMap :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, v} (P ⊞ Q) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, v} P ⊗
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, v} Q :=
  lift (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} biprod.fst) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} biprod.snd)

def dgGluingComplexPinchedBiprodInv :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, v} P ⊗ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, v} Q ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, v} (P ⊞ Q) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedBiprod_isPullback.{u, v} P Q).lift (fst _ _) (snd _ _)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedZero_hom_ext _ _)

lemma dgGluingComplexPinchedBiprodInv_fst :
    dgGluingComplexPinchedBiprodInv.{u, v} P Q ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} biprod.fst =
      fst _ _ :=
  IsPullback.lift_fst _ _ _ _

lemma dgGluingComplexPinchedBiprodInv_snd :
    dgGluingComplexPinchedBiprodInv.{u, v} P Q ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} biprod.snd =
      snd _ _ :=
  IsPullback.lift_snd _ _ _ _

def dgGluingComplexPinchedBiprodIso :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, v} (P ⊞ Q) ≅
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, v} P ⊗ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, v} Q where
  hom := dgGluingComplexPinchedBiprodMap P Q
  inv := dgGluingComplexPinchedBiprodInv P Q
  hom_inv_id := by
    apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedBiprod_isPullback P Q).hom_ext
    · rw [Category.assoc, dgGluingComplexPinchedBiprodInv_fst, Category.id_comp]
      exact lift_fst _ _
    · rw [Category.assoc, dgGluingComplexPinchedBiprodInv_snd, Category.id_comp]
      exact lift_snd _ _
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc]
      change dgGluingComplexPinchedBiprodInv P Q ≫ (lift _ _ ≫ fst _ _) = _
      rw [lift_fst, dgGluingComplexPinchedBiprodInv_fst, Category.id_comp]
    · rw [Category.assoc]
      change dgGluingComplexPinchedBiprodInv P Q ≫ (lift _ _ ≫ snd _ _) = _
      rw [lift_snd, dgGluingComplexPinchedBiprodInv_snd, Category.id_comp]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
