module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.TwoColorStandardPowers
public import SerrePositivity.EInfinity.Operad.TensorFamilyPowerSplitAppend

/-!
# 二色の標準入力の包含とブロック連結

HA 3.2.4.7 の自由比較で、指定二色成分の包含を左右の入力の
テンソル冪の包含と連結で計算する。任意の入力複体の微分を保つ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
variable {A : Type u} [CommRing A]

/-- 一定の添字の生成射は、一定族の同定の後のテンソル冪の射。 -/
lemma tensorFamilyGenerator_constant {I : Type} (Z : Complex A) (D : I → Complex A)
    (e : ∀ i, D i ⟶ Z) (b : I) (r : ℕ) :
    tensorFamilyGenerator Z D e r (fun _ => b) =
      eqToHom (tensorFamily_const (D b) r) ≫ TensorPowers.map (e b) r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change (e b ⊗ₘ tensorFamilyGenerator Z D e r (fun _ => b)) = _
    rw [ih, tensorFamily_const_succ_hom]
    simp only [TensorPowers.map, ← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp]

/-- 一定の添字族への等式を、生成射の始域に反映する。 -/
lemma tensorFamilyGenerator_eq_constant {I : Type} (Z : Complex A) (D : I → Complex A)
    (e : ∀ i, D i ⟶ Z) (b : I) (r : ℕ) (s : Fin r → I) (h : s = fun _ => b) :
    tensorFamilyGenerator Z D e r s =
      eqToHom ((congrArg (fun t => tensorFamily r (fun i => D (t i))) h).trans
        (tensorFamily_const (D b) r)) ≫ TensorPowers.map (e b) r := by
  rw [← tensorFamilyGenerator_index_eq Z D e r h, tensorFamilyGenerator_constant]
  simp only [eqToHom_trans_assoc]

variable (X Y : Complex A)

/-- 標準成分の包含を、左右の冪の包含と指定連結で計算する。 -/
lemma binaryTensorStandardPowersIso_inclusion (m n : ℕ) :
    binaryTensorWordInclusion X Y (m + n) (binaryTensorStandardPattern m n) =
      (binaryTensorStandardPowersIso X Y m n).hom ≫
        (TensorPowers.map (biprod.inl : X ⟶ X ⊞ Y) m ⊗ₘ
          TensorPowers.map (biprod.inr : Y ⟶ X ⊞ Y) n) ≫
        (appendIso (X ⊞ Y) m n).hom := by
  apply (cancel_mono (appendIso (X ⊞ Y) m n).inv).1
  rw [← binaryTensorWordFamilyIso_inclusion X Y (m + n) (binaryTensorStandardPattern m n)]
  have hs := tensorFamilyGenerator_splitToPower (X ⊞ Y) (binaryTensorColorObj X Y)
    (binaryTensorColorInclusion X Y) m n
    (binaryTensorWordColors (m + n) (binaryTensorStandardPattern m n))
  rw [tensorFamilyPowerSplitIso_eq_append] at hs
  simp only [Iso.symm_hom] at hs
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hs]
  have hl : (fun j : Fin m => binaryTensorWordColors (m + n)
      (binaryTensorStandardPattern m n) (j.castAdd n)) = fun _ => false := by
    funext j
    simp [binaryTensorStandardPattern]
  have hr : (fun j : Fin n => binaryTensorWordColors (m + n)
      (binaryTensorStandardPattern m n) (j.natAdd m)) = fun _ => true := by
    funext j
    simp [binaryTensorStandardPattern]
  rw [tensorFamilyGenerator_eq_constant _ _ _ false m _ hl,
    tensorFamilyGenerator_eq_constant _ _ _ true n _ hr]
  simp only [binaryTensorStandardPowersIso, Iso.trans_hom, tensorIso_hom, eqToIso.hom,
    Category.assoc, tensorHom_comp_tensorHom]
  rfl

end SerrePositivity.EInfinity
