module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ComplexPinchedBiprodIso

/-! 同じ直積同型は両鎖射影と、任意の二射の対の全単体作用を厳密に保つ。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory DifferentialGraded
variable {R : Type u} [CommRing R] (P Q : Complex R)

lemma dgGluingComplexPinchedBiprodIso_fst :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedBiprodIso.{u, v} P Q).hom ≫ fst _ _ =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} (biprod.fst : P ⊞ Q ⟶ P) :=
  lift_fst _ _

lemma dgGluingComplexPinchedBiprodIso_snd :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedBiprodIso.{u, v} P Q).hom ≫ snd _ _ =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} (biprod.snd : P ⊞ Q ⟶ Q) :=
  lift_snd _ _

variable {P Q}

lemma dgGluingComplexPinchedBiprodIso_lift {T : Complex R} (a : T ⟶ P) (b : T ⟶ Q) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} (biprod.lift a b) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedBiprodIso.{u, v} P Q).hom =
      lift (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} a) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} b) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, dgGluingComplexPinchedBiprodIso_fst, lift_fst,
      ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_comp, biprod.lift_fst]
  · rw [Category.assoc, dgGluingComplexPinchedBiprodIso_snd, lift_snd,
      ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_comp, biprod.lift_snd]

lemma dgGluingComplexPinchedBiprodIso_projection_pair {T : Complex R} (a : T ⟶ P ⊞ Q) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} a ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedBiprodIso.{u, v} P Q).hom =
      lift (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} (a ≫ biprod.fst))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} (a ≫ biprod.snd)) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, dgGluingComplexPinchedBiprodIso_fst, lift_fst,
      ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_comp]
  · rw [Category.assoc, dgGluingComplexPinchedBiprodIso_snd, lift_snd,
      ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_comp]

lemma dgGluingComplexPinchedBiprodIso_pair_action {P' Q' : Complex R}
    (a : P ⟶ P') (b : Q ⟶ Q') :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} (biprod.lift (biprod.fst ≫ a) (biprod.snd ≫ b)) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedBiprodIso.{u, v} P' Q').hom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedBiprodIso.{u, v} P Q).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} a ⊗ₘ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} b) := by
  rw [dgGluingComplexPinchedBiprodIso_lift]
  apply CartesianMonoidalCategory.hom_ext
  · rw [lift_fst, Category.assoc, tensorHom_fst, ← Category.assoc,
      dgGluingComplexPinchedBiprodIso_fst, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_comp]
  · rw [lift_snd, Category.assoc, tensorHom_snd, ← Category.assoc,
      dgGluingComplexPinchedBiprodIso_snd, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_comp]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
