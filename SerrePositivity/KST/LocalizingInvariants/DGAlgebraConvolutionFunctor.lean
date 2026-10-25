module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConvolutionAlgebraMap

/-!
概要：実余モノイド射の反変な畳み込み代数射を構成する。
方針：評価の自然性と対角の保存を閉構造の転置に反映する。
規約：元の内部 Hom 前合成を底の射として使う。
使われ方：AW 単体に対する乗法的 frame の関手性。
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
variable (R : Type u) [CommRing R] {H K : Comon (Complex R)}

lemma convolutionPrecompose_mul (f : H ⟶ K) (B : Mon (Complex R)) :
    μ[((convolutionFunctor R K).obj B).X] ≫ (MonoidalClosed.pre f.hom).app B.X =
      ((MonoidalClosed.pre f.hom).app B.X ⊗ₘ (MonoidalClosed.pre f.hom).app B.X) ≫
        μ[((convolutionFunctor R H).obj B).X] := by
  let p := (MonoidalClosed.pre f.hom).app B.X
  have hn : H.X ◁ (p ⊗ₘ p) ≫ Functor.OplaxMonoidal.δ (convolutionTensor R H)
      ((ihom H.X).obj B.X) ((ihom H.X).obj B.X) =
      Functor.OplaxMonoidal.δ (convolutionTensor R H)
        ((ihom K.X).obj B.X) ((ihom K.X).obj B.X) ≫
        (H.X ◁ p ⊗ₘ H.X ◁ p) := by
    simpa [convolutionTensor, convolutionConstant] using
      (Functor.OplaxMonoidal.δ_natural (convolutionTensor R H) p p).symm
  have he : H.X ◁ p ≫ (ihom.ev H.X).app B.X =
      f.hom ▷ ((ihom K.X).obj B.X) ≫ (ihom.ev K.X).app B.X :=
    MonoidalClosed.id_tensor_pre_app_comp_ev f.hom B.X
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_pre_app, MonoidalClosed.uncurry_natural_left,
    convolutionFunctor_mul, convolutionFunctor_mul,
    convolutionAdjunction_homEquiv, convolutionAdjunction_homEquiv,
    MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_curry,
    convolutionAdjunction_counit, convolutionAdjunction_counit]
  change f.hom ▷ _ ≫ _ ≫ _ ≫ B.mon.mul = H.X ◁ (p ⊗ₘ p) ≫ _ ≫ _ ≫ B.mon.mul
  rw [← Category.assoc (H.X ◁ (p ⊗ₘ p)), hn]
  simp only [Category.assoc]
  rw [tensorHom_comp_tensorHom_assoc, he, ← tensorHom_comp_tensorHom_assoc]
  simpa only [Category.assoc] using congrArg
    (fun t => t ≫ ((ihom.ev K.X).app B.X ⊗ₘ (ihom.ev K.X).app B.X) ≫ B.mon.mul)
    (convolutionTensor_pre_delta R f ((ihom K.X).obj B.X) ((ihom K.X).obj B.X))

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
