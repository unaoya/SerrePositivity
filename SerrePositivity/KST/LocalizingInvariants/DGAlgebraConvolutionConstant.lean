module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConvolutionConstantTensor
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConvolutionMaps

/-!
概要：実余単位から内部 Hom の定数単体を構成する。
方針：tensor の全余単位比較を閉構造で転置する。
規約：元の代数射と底を保ち、収縮の存在を入力にしない。
使われ方：指定された底射上の相対写像の単体集合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory
open scoped MonObj
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (H : Comon (Complex R)) (B : Mon (Complex R))

def convolutionConstantHom : B.X ⟶ ((convolutionFunctor R H).obj B).X :=
  MonoidalClosed.curry (A := H.X) ((convolutionTensorCounit R H).app B.X)

lemma convolutionConstantHom_one :
    B.mon.one ≫ convolutionConstantHom R H B = η[((convolutionFunctor R H).obj B).X] := by
  rw [convolutionConstantHom, ← MonoidalClosed.curry_natural_left,
    convolutionFunctor_one, convolutionAdjunction_homEquiv]
  congr 1
  have h : H.X ◁ B.mon.one ≫ (convolutionTensorCounit R H).app B.X =
      (convolutionTensorCounit R H).app (𝟙_ (Complex R)) ≫ B.mon.one := by
    exact (convolutionTensorCounit R H).naturality B.mon.one
  rw [h, convolutionTensorCounit_unit]

lemma convolutionConstantHom_mul :
    B.mon.mul ≫ convolutionConstantHom R H B =
      (convolutionConstantHom R H B ⊗ₘ convolutionConstantHom R H B) ≫
        μ[((convolutionFunctor R H).obj B).X] := by
  let p : B.X ⟶ (ihom H.X).obj B.X := convolutionConstantHom R H B
  have hn : H.X ◁ (p ⊗ₘ p) ≫ Functor.OplaxMonoidal.δ (convolutionTensor R H)
      ((ihom H.X).obj B.X) ((ihom H.X).obj B.X) =
      Functor.OplaxMonoidal.δ (convolutionTensor R H) B.X B.X ≫
        (H.X ◁ p ⊗ₘ H.X ◁ p) := by
    exact (Functor.OplaxMonoidal.δ_natural (convolutionTensor R H) p p).symm
  have he : H.X ◁ p ≫ (ihom.ev H.X).app B.X = (convolutionTensorCounit R H).app B.X :=
    MonoidalClosed.whiskerLeft_curry_ihom_ev_app (A := H.X) B.X
      ((convolutionTensorCounit R H).app B.X)
  have hb : H.X ◁ B.mon.mul ≫ (convolutionTensorCounit R H).app B.X =
      (convolutionTensorCounit R H).app (B.X ⊗ B.X) ≫ B.mon.mul := by
    exact (convolutionTensorCounit R H).naturality B.mon.mul
  have hp : MonoidalClosed.uncurry p = (convolutionTensorCounit R H).app B.X :=
    MonoidalClosed.uncurry_curry (A := H.X) ((convolutionTensorCounit R H).app B.X)
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_left,
    convolutionFunctor_mul, convolutionAdjunction_homEquiv,
    MonoidalClosed.uncurry_curry, convolutionAdjunction_counit]
  change H.X ◁ B.mon.mul ≫ MonoidalClosed.uncurry p = H.X ◁ (p ⊗ₘ p) ≫ _ ≫ _ ≫ B.mon.mul
  rw [hp, hb, ← Category.assoc (H.X ◁ (p ⊗ₘ p)), hn]
  simp only [Category.assoc]
  rw [tensorHom_comp_tensorHom_assoc, he]
  simpa only [CategoryTheory.Functor.id_obj, Category.assoc] using congrArg (fun t => t ≫ B.mon.mul)
    (convolutionTensorCounit_tensor R H B.X B.X).symm

def convolutionConstantMap : B ⟶ (convolutionFunctor R H).obj B :=
  Mon.Hom.mk' (convolutionConstantHom R H B)
    (convolutionConstantHom_one R H B) (convolutionConstantHom_mul R H B)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
