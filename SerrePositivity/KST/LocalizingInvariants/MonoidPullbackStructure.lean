module

public import SerrePositivity.KST.LocalizingInvariants.MonoidObjectAlongFamily
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
概要：実モノイド対象の pullback に、元の単位と積を持ち上げる。
方針：underlying pullback の両射影を共同単射族として使い、代数則を検証する。
規約：tensor の極限保存は不要。使われ方：非可換 dg 代数の相対経路。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits MonoidalCategory
open scoped MonObj
namespace SerrePositivity.KST.LocalizingInvariants.MonoidPullback
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {A B D : Mon C} (f : A ⟶ D) (g : B ⟶ D) [HasPullback f.hom g.hom]

abbrev carrier : C := pullback f.hom g.hom

def one : 𝟙_ C ⟶ carrier f g :=
  pullback.lift η[A.X] η[B.X] (by rw [IsMonHom.one_hom, IsMonHom.one_hom])

lemma mul_comm :
    (((pullback.fst f.hom g.hom) ⊗ₘ (pullback.fst f.hom g.hom)) ≫ μ[A.X]) ≫ f.hom =
      (((pullback.snd f.hom g.hom) ⊗ₘ (pullback.snd f.hom g.hom)) ≫ μ[B.X]) ≫ g.hom := by
  rw [Category.assoc, IsMonHom.mul_hom, ← Category.assoc, tensorHom_comp_tensorHom,
    pullback.condition, Category.assoc, IsMonHom.mul_hom, ← Category.assoc,
    tensorHom_comp_tensorHom]

def mul : carrier f g ⊗ carrier f g ⟶ carrier f g :=
  pullback.lift ((pullback.fst f.hom g.hom ⊗ₘ pullback.fst f.hom g.hom) ≫ μ[A.X])
    ((pullback.snd f.hom g.hom ⊗ₘ pullback.snd f.hom g.hom) ≫ μ[B.X]) (mul_comm f g)

@[reassoc]
lemma one_fst : one f g ≫ pullback.fst f.hom g.hom = η[A.X] := pullback.lift_fst _ _ _

@[reassoc]
lemma one_snd : one f g ≫ pullback.snd f.hom g.hom = η[B.X] := pullback.lift_snd _ _ _

@[reassoc]
lemma mul_fst : mul f g ≫ pullback.fst f.hom g.hom =
    (pullback.fst f.hom g.hom ⊗ₘ pullback.fst f.hom g.hom) ≫ μ[A.X] := pullback.lift_fst _ _ _

@[reassoc]
lemma mul_snd : mul f g ≫ pullback.snd f.hom g.hom =
    (pullback.snd f.hom g.hom ⊗ₘ pullback.snd f.hom g.hom) ≫ μ[B.X] := pullback.lift_snd _ _ _

def obj : Mon C where
  X := carrier f g
  mon := by
    let Bs : Bool → Mon C := fun j => if j then B else A
    let ps : ∀ j, carrier f g ⟶ (Bs j).X := fun j => by
      cases j
      · exact pullback.fst f.hom g.hom
      · exact pullback.snd f.hom g.hom
    refine monoidObjectAlongFamily Bs ps ?_ (one f g) (mul f g) ?_ ?_
    · intro T a b h
      exact pullback.hom_ext (h false) (h true)
    · intro j; cases j
      · exact one_fst f g
      · exact one_snd f g
    · intro j; cases j
      · exact mul_fst f g
      · exact mul_snd f g

def fst : obj f g ⟶ A :=
  Mon.Hom.mk' (pullback.fst f.hom g.hom) (one_fst f g) (mul_fst f g)

def snd : obj f g ⟶ B :=
  Mon.Hom.mk' (pullback.snd f.hom g.hom) (one_snd f g) (mul_snd f g)

lemma condition : fst f g ≫ f = snd f g ≫ g := by
  apply Mon.Hom.ext
  exact pullback.condition

end SerrePositivity.KST.LocalizingInvariants.MonoidPullback
