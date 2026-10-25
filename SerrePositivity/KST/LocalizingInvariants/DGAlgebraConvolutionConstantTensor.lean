module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConvolutionPrecompose

/-!
概要：実余単位から tensor 関手の定数単体用の比較を構成する。
方針：元の余単位射と単位子の全自然性を合成する。
規約：AW 収縮の存在や同定を入力にしない。
使われ方：指定底への定数単体と相対写像模型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory
open scoped ComonObj
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
private lemma unitTensorCoherence {C : Type v} [Category.{w} C] [MonoidalCategory C]
    [BraidedCategory C] (X Y : C) :
    ((λ_ (𝟙_ C)).inv ⊗ₘ 𝟙 (X ⊗ Y)) ≫ tensorδ (𝟙_ C) X (𝟙_ C) Y ≫
      ((λ_ X).hom ⊗ₘ (λ_ Y).hom) = (λ_ (X ⊗ Y)).hom := by
  rw [leftUnitor_monoidal]
  simp only [tensorHom_id, tensorδ_tensorμ_assoc,
    ← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight, Category.id_comp]

private lemma counitTensorCoherence {C : Type v} [Category.{w} C] [MonoidalCategory C]
    [BraidedCategory C] (H : Comon C) (X Y : C) :
    (Δ[H.X] ⊗ₘ 𝟙 (X ⊗ Y)) ≫ tensorδ H.X X H.X Y ≫
      ((ε[H.X] ▷ X ≫ (λ_ X).hom) ⊗ₘ (ε[H.X] ▷ Y ≫ (λ_ Y).hom)) =
      ε[H.X] ▷ (X ⊗ Y) ≫ (λ_ (X ⊗ Y)).hom := by
  let : MonoidalCategory (C × C) := MonoidalCategory.prodMonoidal C C
  have hn : tensorδ H.X X H.X Y ≫ (ε[H.X] ▷ X ⊗ₘ ε[H.X] ▷ Y) =
      ((ε[H.X] ⊗ₘ ε[H.X]) ⊗ₘ 𝟙 (X ⊗ Y)) ≫ tensorδ (𝟙_ C) X (𝟙_ C) Y := by
    simpa using (Functor.OplaxMonoidal.δ_natural (tensor C)
      (show (H.X, X) ⟶ (𝟙_ C, X) from (ε[H.X], 𝟙 X))
      (show (H.X, Y) ⟶ (𝟙_ C, Y) from (ε[H.X], 𝟙 Y)))
  have hc := (IsComonHom.hom_comul (default : H ⟶ Comon.trivial C).hom).symm
  change Δ[H.X] ≫ (ε[H.X] ⊗ₘ ε[H.X]) = ε[H.X] ≫ (λ_ (𝟙_ C)).inv at hc
  have hp := congrArg (fun t => (Δ[H.X] ⊗ₘ 𝟙 (X ⊗ Y)) ≫ t ≫
    ((λ_ X).hom ⊗ₘ (λ_ Y).hom)) hn
  simp only [Category.assoc] at hp
  rw [tensorHom_comp_tensorHom_assoc, Category.comp_id, hc] at hp
  simp only [tensorHom_id, comp_whiskerRight, Category.assoc] at hp
  have hu := unitTensorCoherence X Y
  simp only [tensorHom_id] at hu
  rw [hu] at hp
  simpa only [tensorHom_id, ← tensorHom_comp_tensorHom, Category.assoc] using hp

variable (R : Type u) [CommRing R]

def convolutionTensorCounit (H : Comon (Complex R)) : convolutionTensor R H ⟶ 𝟭 (Complex R) :=
  (convolutionTensorIso R H).inv ≫ (tensoringLeft (Complex R)).map ε[H.X] ≫
    (leftUnitorNatIso (Complex R)).hom

lemma convolutionTensorCounit_app (H : Comon (Complex R)) (X : Complex R) :
    (convolutionTensorCounit R H).app X = ε[H.X] ▷ X ≫ (λ_ X).hom := by
  change (𝟙 _) ≫ ε[H.X] ▷ X ≫ (λ_ X).hom = _
  exact Category.id_comp _

lemma convolutionTensorCounit_unit (H : Comon (Complex R)) :
    Functor.OplaxMonoidal.η (convolutionTensor R H) =
      (convolutionTensorCounit R H).app (𝟙_ (Complex R)) := by
  rw [convolutionTensor_eta, convolutionTensorCounit_app]
  simp only [tensorHom_id]

lemma convolutionTensorCounit_tensor (H : Comon (Complex R)) (X Y : Complex R) :
    Functor.OplaxMonoidal.δ (convolutionTensor R H) X Y ≫
      ((convolutionTensorCounit R H).app X ⊗ₘ (convolutionTensorCounit R H).app Y) =
      (convolutionTensorCounit R H).app (X ⊗ Y) := by
  rw [convolutionTensor_delta, convolutionTensorCounit_app,
    convolutionTensorCounit_app, convolutionTensorCounit_app]
  simpa only [convolutionTensor, convolutionConstant, Functor.comp_obj, Functor.prod'_obj,
    Functor.id_obj, Functor.const_obj_obj, tensor_obj, Category.assoc] using
    (counitTensorCoherence H X Y)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
