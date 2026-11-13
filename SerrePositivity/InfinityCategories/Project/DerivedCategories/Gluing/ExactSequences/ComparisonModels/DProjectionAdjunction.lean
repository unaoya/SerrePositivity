module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomotopyRepresentations.FactorHomotopySections
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Models.HomotopyProjectionHoms
public import Mathlib.CategoryTheory.Adjunction.Basic

/-! 同じ D 切断と右射影の実 H⁰ 随伴を、元の Hom 射影から構成する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C)
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M
local notation "P" => DGFunctor.onHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D M)
local notation "S" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDSectionHomotopy R C D M hC
local notation "ε" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDSectionProjectionIso R C D M hC

/-- 右射影の同じ射写像と切断余単位から得る、随伴の Hom 全単射。 -/
def dgGluingDProjectionHomEquiv (X : HomotopyCategory R D) (Y : HomotopyCategory R G) :
    ((S).obj X ⟶ Y) ≃ (X ⟶ (P).obj Y) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomotopyHomEquiv R C D M
    (ForgetEnrichment.to (Complex R) ((S).obj X).as)
    (ForgetEnrichment.to (Complex R) Y.as)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDSectionHomotopy_left_zero R C D M hC X)).trans
      (Iso.homCongr ((ε).app X) (Iso.refl ((P).obj Y)))

lemma dgGluingDProjectionHomEquiv_apply
    (X : HomotopyCategory R D) (Y : HomotopyCategory R G) (f : (S).obj X ⟶ Y) :
    dgGluingDProjectionHomEquiv R C D M hC X Y f =
      ((ε).app X).inv ≫ (P).map f := by
  change ((ε).app X).inv ≫ (P).map f ≫ 𝟙 _ = _
  rw [Category.comp_id]

/-- 同じ D 切断関手は、元の右射影に左随伴。 -/
def dgGluingDProjectionAdjunction : S ⊣ P :=
  Adjunction.mkOfHomEquiv
    { homEquiv := dgGluingDProjectionHomEquiv R C D M hC
      homEquiv_naturality_left_symm := by
        intro X' X Y f g
        apply (dgGluingDProjectionHomEquiv R C D M hC X' Y).injective
        rw [Equiv.apply_symm_apply, dgGluingDProjectionHomEquiv_apply,
          CategoryTheory.Functor.map_comp]
        have hn := (ε).inv.naturality f
        change f ≫ ((ε).app X).inv = ((ε).app X').inv ≫ (P).map ((S).map f) at hn
        rw [← Category.assoc, ← hn, Category.assoc]
        rw [← dgGluingDProjectionHomEquiv_apply, Equiv.apply_symm_apply]
      homEquiv_naturality_right := by
        intro X Y Y' f g
        simp only [dgGluingDProjectionHomEquiv_apply,
          CategoryTheory.Functor.map_comp, Category.assoc] }

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
