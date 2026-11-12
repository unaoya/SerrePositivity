module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.FactorHomotopySections
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomotopyProjectionHoms
public import Mathlib.CategoryTheory.Adjunction.Basic

/-! 同じ左射影と C 切断の実 H⁰ 随伴を、元の Hom 射影から構成する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D)
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M
local notation "L" => DGFunctor.onHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D M)
local notation "S" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCSectionHomotopy R C D M hD
local notation "ε" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCSectionProjectionIso R C D M hD

/-- 左射影の同じ射写像と切断余単位から得る、随伴の Hom 全単射。 -/
def dgGluingCProjectionHomEquiv (X : HomotopyCategory R G) (Y : HomotopyCategory R C) :
    ((L).obj X ⟶ Y) ≃ (X ⟶ (S).obj Y) :=
  ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomotopyHomEquiv R C D M
    (ForgetEnrichment.to (Complex R) X.as)
    (ForgetEnrichment.to (Complex R) ((S).obj Y).as)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCSectionHomotopy_right_zero R C D M hD Y)).trans
      (Iso.homCongr (Iso.refl ((L).obj X)) ((ε).app Y))).symm

lemma dgGluingCProjectionHomEquiv_symm_apply
    (X : HomotopyCategory R G) (Y : HomotopyCategory R C) (f : X ⟶ (S).obj Y) :
    (dgGluingCProjectionHomEquiv R C D M hD X Y).symm f =
      (L).map f ≫ ((ε).app Y).hom := by
  change 𝟙 _ ≫ (L).map f ≫ ((ε).app Y).hom = _
  rw [Category.id_comp]

/-- 元の左射影は、同じ C 切断関手に左随伴。 -/
def dgGluingCProjectionAdjunction : L ⊣ S :=
  Adjunction.mkOfHomEquiv
    { homEquiv := dgGluingCProjectionHomEquiv R C D M hD
      homEquiv_naturality_left_symm := by
        intro X' X Y f g
        simp only [dgGluingCProjectionHomEquiv_symm_apply,
          CategoryTheory.Functor.map_comp, Category.assoc]
      homEquiv_naturality_right := by
        intro X Y Y' f g
        apply (dgGluingCProjectionHomEquiv R C D M hD X Y').symm.injective
        rw [Equiv.symm_apply_apply, dgGluingCProjectionHomEquiv_symm_apply,
          CategoryTheory.Functor.map_comp, Category.assoc]
        have hn := (ε).hom.naturality g
        change (L).map ((S).map g) ≫ ((ε).app Y').hom = ((ε).app Y).hom ≫ g at hn
        rw [hn, ← Category.assoc]
        rw [← dgGluingCProjectionHomEquiv_symm_apply, Equiv.symm_apply_apply] }

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
