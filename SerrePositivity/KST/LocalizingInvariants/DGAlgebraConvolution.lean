module

public import SerrePositivity.DifferentialGraded.Complexes.HomLimits
public import Mathlib.CategoryTheory.Monoidal.Comon_
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
概要：複体の実余モノイドから dg 代数の内部 Hom 畳み込みを構成する。
方針：余モノイドの定値 oplax 関手と tensor の合成の右随伴を使う。
規約：余モノイドの余結合・余単位を入力に含め、AW の構成を複製しない。
使われ方：単体の実余モノイドから乗法的単体 frame を作る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory
open scoped ComonObj MonObj
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (H : Comon (Complex R))

local instance : MonoidalCategory (Complex R × Complex R) :=
  MonoidalCategory.prodMonoidal (Complex R) (Complex R)

def convolutionConstant : Complex R ⥤ Complex R :=
  (Functor.const (Complex R)).obj H.X

instance convolutionConstant_oplax : (convolutionConstant R H).OplaxMonoidal where
  «η» := ε[H.X]
  δ _ _ := Δ[H.X]
  δ_natural_left _ _ := by simp [convolutionConstant]
  δ_natural_right _ _ := by simp [convolutionConstant]
  oplax_associativity _ _ _ := by
    simp [convolutionConstant]
  oplax_left_unitality _ := by
    simp [convolutionConstant]
  oplax_right_unitality _ := by
    simp [convolutionConstant]

def convolutionTensor : Complex R ⥤ Complex R :=
  (Functor.prod' (convolutionConstant R H) (𝟭 (Complex R))) ⋙ tensor (Complex R)

instance convolutionTensor_oplax : (convolutionTensor R H).OplaxMonoidal := by
  letI : (convolutionConstant R H).OplaxMonoidal := convolutionConstant_oplax R H
  letI : (Functor.prod' (convolutionConstant R H) (𝟭 (Complex R))).OplaxMonoidal := inferInstance
  letI : (tensor (Complex R)).Monoidal := inferInstance
  unfold convolutionTensor
  infer_instance

def convolutionTensorIso : tensorLeft H.X ≅ convolutionTensor R H :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    simp [convolutionTensor, convolutionConstant])

def convolutionAdjunction : convolutionTensor R H ⊣ ihom H.X :=
  (ihom.adjunction H.X).ofNatIsoLeft (convolutionTensorIso R H)

instance convolutionHom_lax : (ihom H.X).LaxMonoidal :=
  (convolutionAdjunction R H).rightAdjointLaxMonoidal

def convolutionFunctor : Mon (Complex R) ⥤ Mon (Complex R) :=
  (ihom H.X).mapMon

lemma convolutionFunctor_obj_X (B : Mon (Complex R)) :
    ((convolutionFunctor R H).obj B).X = (ihom H.X).obj B.X := rfl

lemma convolutionFunctor_map_hom {B C : Mon (Complex R)} (f : B ⟶ C) :
    ((convolutionFunctor R H).map f).hom = (ihom H.X).map f.hom := rfl

lemma convolutionFunctor_obj_homComplex (B : Mon (Complex R)) :
    ((convolutionFunctor R H).obj B).X = homComplex R H.X B.X := rfl

lemma convolutionFunctor_one (B : Mon (Complex R)) :
    η[((convolutionFunctor R H).obj B).X] =
      (convolutionAdjunction R H).homEquiv _ _
        (Functor.OplaxMonoidal.η (convolutionTensor R H) ≫ B.mon.one) := by
  change (convolutionAdjunction R H).homEquiv _ _ _ ≫ (ihom H.X).map B.mon.one = _
  exact ((convolutionAdjunction R H).homEquiv_naturality_right _ _).symm

lemma convolutionFunctor_mul (B : Mon (Complex R)) :
    μ[((convolutionFunctor R H).obj B).X] =
      (convolutionAdjunction R H).homEquiv _ _
        (Functor.OplaxMonoidal.δ (convolutionTensor R H)
          ((ihom H.X).obj B.X) ((ihom H.X).obj B.X) ≫
          ((convolutionAdjunction R H).counit.app B.X ⊗ₘ
            (convolutionAdjunction R H).counit.app B.X) ≫ B.mon.mul) := by
  change (convolutionAdjunction R H).homEquiv _ _ _ ≫ (ihom H.X).map B.mon.mul = _
  simpa only [CategoryTheory.Functor.id_obj, Category.assoc] using
    ((convolutionAdjunction R H).homEquiv_naturality_right
    (Functor.OplaxMonoidal.δ (convolutionTensor R H)
      ((ihom H.X).obj B.X) ((ihom H.X).obj B.X) ≫
      ((convolutionAdjunction R H).counit.app B.X ⊗ₘ
        (convolutionAdjunction R H).counit.app B.X)) B.mon.mul).symm

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
