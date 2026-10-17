module
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtensionLeftMaps
public import SerrePositivity.DifferentialGraded.Tensor.Ring

/-! # 一対象環での相対 tensor の係数変更と通常 tensor の比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory MonoidalCategory Opposite
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (M : RightModule A PUnit.{1}) (N : LeftModule A PUnit.{1})

/-- 一対象環の係数変更後の相対 tensor を、値の通常 tensor と比較する。 -/
def ringBalancedIso :
    BalancedTensor.obj A' (DGBaseChange φ PUnit.{1})
        (rightModule φ PUnit.{1} M) (leftModule φ PUnit.{1} N) ≅
      (extension φ).obj (M.obj (op PUnit.unit)) ⊗ (extension φ).obj (N.obj PUnit.unit) :=
  (balancedIso φ PUnit.{1} M N).symm ≪≫
    (extension φ).mapIso (BalancedTensor.ringIso A M N) ≪≫
      tensorIso φ (M.obj (op PUnit.unit)) (N.obj PUnit.unit)

/-- 唯一の対象の生成項を恒等写像へ送る、通常 tensor の標準的比較である。 -/
@[reassoc (attr := simp)]
lemma ι_ringBalancedIso :
    BalancedTensor.ι A' (DGBaseChange φ PUnit.{1})
        (rightModule φ PUnit.{1} M) (leftModule φ PUnit.{1} N) PUnit.unit ≫
      (ringBalancedIso φ M N).hom = 𝟙 _ := by
  simp only [ringBalancedIso, Iso.trans_hom, Iso.symm_hom,
    CategoryTheory.Functor.mapIso_hom]
  rw [balancedIso_inv_ι_assoc, ← CategoryTheory.Functor.map_comp_assoc,
    BalancedTensor.ι_ringIso_hom, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id]

@[reassoc]
lemma ringBalancedIso_comparison :
    (balancedIso φ PUnit.{1} M N).hom ≫ (ringBalancedIso φ M N).hom =
      (extension φ).map (BalancedTensor.ringIso A M N).hom ≫
        (tensorIso φ (M.obj (op PUnit.unit)) (N.obj PUnit.unit)).hom := by
  simp only [ringBalancedIso, Iso.trans_hom, Iso.symm_hom,
    Iso.hom_inv_id_assoc, CategoryTheory.Functor.mapIso_hom]

/-- 元の一対象加群が複体から来る場合の、非有界な通常 tensor との比較。 -/
abbrev ringComplexBaseChangeIso (P Q : Complex A) :=
  ringBalancedIso φ (ringModule A P) (ringLeftModule A Q)

lemma ringComplexBaseChange_comparison (P Q : Complex A) :
    (extension φ).map (BalancedTensor.ringComplexTensorIso A P Q).hom ≫
        (cochainTensorBaseChangeIso φ P Q).hom =
      (balancedIso φ PUnit.{1} (ringModule A P) (ringLeftModule A Q)).hom ≫
        (ringComplexBaseChangeIso φ P Q).hom :=
  (ringBalancedIso_comparison φ (ringModule A P) (ringLeftModule A Q)).symm

end SerrePositivity.DifferentialGraded.ScalarExtension
