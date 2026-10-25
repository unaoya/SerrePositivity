module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConvolution

/-!
概要：余モノイド射による畳み込み代数の前合成を扱う。
方針：元の内部 Hom 前合成を、余単位と対角の保存式で代数射へ持ち上げる。
規約：AW 単体射の構成は E2 の正本を使う。
使われ方：乗法的単体 frame の面・退化射。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory
open scoped ComonObj
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R]
local instance : MonoidalCategory (Complex R × Complex R) :=
  MonoidalCategory.prodMonoidal (Complex R) (Complex R)

lemma convolutionTensor_eta (H : Comon (Complex R)) :
    Functor.OplaxMonoidal.η (convolutionTensor R H) =
      (ε[H.X] ⊗ₘ 𝟙 (𝟙_ (Complex R))) ≫ (λ_ (𝟙_ (Complex R))).hom := by
  simp [convolutionTensor, Functor.OplaxMonoidal.comp_η,
    tensor_map]
  rfl

lemma convolutionTensor_delta (H : Comon (Complex R)) (X Y : Complex R) :
    Functor.OplaxMonoidal.δ (convolutionTensor R H) X Y =
      (Δ[H.X] ⊗ₘ 𝟙 (X ⊗ Y)) ≫ tensorδ H.X X H.X Y := by
  simp [convolutionTensor, Functor.OplaxMonoidal.comp_δ,
    tensor_map]
  rfl

lemma convolutionTensor_eta_counit (H : Comon (Complex R)) :
    Functor.OplaxMonoidal.η (convolutionTensor R H) = (ρ_ H.X).hom ≫ ε[H.X] := by
  rw [convolutionTensor_eta]
  simp [unitors_equal]

lemma convolutionTensor_pre_eta {H K : Comon (Complex R)} (f : H ⟶ K) :
    f.hom ▷ (𝟙_ (Complex R)) ≫ Functor.OplaxMonoidal.η (convolutionTensor R K) =
      Functor.OplaxMonoidal.η (convolutionTensor R H) := by
  rw [convolutionTensor_eta_counit, convolutionTensor_eta_counit,
    ← Category.assoc, rightUnitor_naturality]
  simp

lemma convolutionTensor_pre_delta {H K : Comon (Complex R)} (f : H ⟶ K)
    (X Y : Complex R) :
    f.hom ▷ (X ⊗ Y) ≫ Functor.OplaxMonoidal.δ (convolutionTensor R K) X Y =
      Functor.OplaxMonoidal.δ (convolutionTensor R H) X Y ≫
        (f.hom ▷ X ⊗ₘ f.hom ▷ Y) := by
  have ht : tensorδ H.X X H.X Y ≫ (f.hom ▷ X ⊗ₘ f.hom ▷ Y) =
      ((f.hom ⊗ₘ f.hom) ⊗ₘ 𝟙 (X ⊗ Y)) ≫ tensorδ K.X X K.X Y := by
    simpa using (Functor.OplaxMonoidal.δ_natural (tensor (Complex R))
      (show (H.X, X) ⟶ (K.X, X) from (f.hom, 𝟙 X))
      (show (H.X, Y) ⟶ (K.X, Y) from (f.hom, 𝟙 Y)))
  simp only [tensorHom_id] at ht
  rw [convolutionTensor_delta, convolutionTensor_delta]
  simp only [tensorHom_id]
  rw [← comp_whiskerRight_assoc, IsComonHom.hom_comul, comp_whiskerRight,
    Category.assoc, ← ht]
  simp only [Category.assoc]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
