module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexPinchedBiprodIso

/-! 同じ直積同型は両鎖射影と、任意の二射の対の全単体作用を厳密に保つ。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory DifferentialGraded
variable {R : Type u} [CommRing R] (P Q : Complex R)

lemma dgGluingComplexPinchedBiprodIso_fst :
    (dgGluingComplexPinchedBiprodIso.{u, v} P Q).hom ≫ fst _ _ =
      complexPinchedMap.{u, v} (biprod.fst : P ⊞ Q ⟶ P) :=
  lift_fst _ _

lemma dgGluingComplexPinchedBiprodIso_snd :
    (dgGluingComplexPinchedBiprodIso.{u, v} P Q).hom ≫ snd _ _ =
      complexPinchedMap.{u, v} (biprod.snd : P ⊞ Q ⟶ Q) :=
  lift_snd _ _

variable {P Q}

lemma dgGluingComplexPinchedBiprodIso_lift {T : Complex R} (a : T ⟶ P) (b : T ⟶ Q) :
    complexPinchedMap.{u, v} (biprod.lift a b) ≫
        (dgGluingComplexPinchedBiprodIso.{u, v} P Q).hom =
      lift (complexPinchedMap.{u, v} a) (complexPinchedMap.{u, v} b) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, dgGluingComplexPinchedBiprodIso_fst, lift_fst,
      ← complexPinchedMap_comp, biprod.lift_fst]
  · rw [Category.assoc, dgGluingComplexPinchedBiprodIso_snd, lift_snd,
      ← complexPinchedMap_comp, biprod.lift_snd]

lemma dgGluingComplexPinchedBiprodIso_projection_pair {T : Complex R} (a : T ⟶ P ⊞ Q) :
    complexPinchedMap.{u, v} a ≫ (dgGluingComplexPinchedBiprodIso.{u, v} P Q).hom =
      lift (complexPinchedMap.{u, v} (a ≫ biprod.fst))
        (complexPinchedMap.{u, v} (a ≫ biprod.snd)) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, dgGluingComplexPinchedBiprodIso_fst, lift_fst,
      ← complexPinchedMap_comp]
  · rw [Category.assoc, dgGluingComplexPinchedBiprodIso_snd, lift_snd,
      ← complexPinchedMap_comp]

lemma dgGluingComplexPinchedBiprodIso_pair_action {P' Q' : Complex R}
    (a : P ⟶ P') (b : Q ⟶ Q') :
    complexPinchedMap.{u, v} (biprod.lift (biprod.fst ≫ a) (biprod.snd ≫ b)) ≫
        (dgGluingComplexPinchedBiprodIso.{u, v} P' Q').hom =
      (dgGluingComplexPinchedBiprodIso.{u, v} P Q).hom ≫
        (complexPinchedMap.{u, v} a ⊗ₘ complexPinchedMap.{u, v} b) := by
  rw [dgGluingComplexPinchedBiprodIso_lift]
  apply CartesianMonoidalCategory.hom_ext
  · rw [lift_fst, Category.assoc, tensorHom_fst, ← Category.assoc,
      dgGluingComplexPinchedBiprodIso_fst, ← complexPinchedMap_comp]
  · rw [lift_snd, Category.assoc, tensorHom_snd, ← Category.assoc,
      dgGluingComplexPinchedBiprodIso_snd, ← complexPinchedMap_comp]

end SerrePositivity.InfinityCategories
