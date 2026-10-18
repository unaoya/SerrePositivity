module

public import SerrePositivity.EInfinity.Operad.TensorSubstitutionParallel
public import SerrePositivity.EInfinity.Operad.TensorSubstitutionBlocks
public import SerrePositivity.EInfinity.Operad.TensorSubstitutionEmptyTail

/-!
# 異なる入力への有限族のテンソル代入

概要：Berger–Moerdijk §1 の異なる入力への交換則を有限族の末尾からの代入へ拡張する。
方針：最後の因子の分離と係数射を交換し、二段の平行な代入の比較を適用する。
規約：先頭へ代入する係数 U を有限入力族全体の後へ移す。
使われ方：先頭への合成と後半の反復合成を交換する帰納段階を処理する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A]

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：後半の入力族が空なら平行な代入の比較は右単位子の式となる（Berger–Moerdijk §1）。
方針：外側の結合子を右単位子で表し、空の後半の代入の相殺則を使う。
規約：係数の移送 a を空の代入の後へ合成してよい。
使われ方：先頭の合成と後半の反復代入の交換則の空の族の基底を処理する。 -/
lemma tensorSubstitutionStep_parallel_unit {R R₁ U O : Complex A}
    (a : R ⟶ R₁) (f : R₁ ⊗ U ⟶ O) :
    (α_ R U (𝟙_ (Complex A))).hom ≫ tensorSubstitutionStep ((ρ_ R).hom ≫ a) f =
      (ρ_ (R ⊗ U)).hom ≫ (a ▷ U) ≫ f := by
  have hc : (α_ R U (𝟙_ (Complex A))).hom =
      (ρ_ (R ⊗ U)).hom ≫ (R ◁ (ρ_ U).inv) := by monoidal
  rw [hc, Category.assoc, tensorSubstitutionStep_empty_tail]

/-- 概要：一段の代入と前半の代入の交換則から有限族全体の交換則を得る（Berger–Moerdijk §1）。
方針：末尾分離の自然性と二段の平行なテンソル代入の比較を組み合わせる。
規約：入力族 V の最後の因子と残りの因子の順序を保つ。
使われ方：オペラッドの平行な部分合成の交換則を後半の有限入力族へ帰納的に拡張する。 -/
lemma tensorFamilySubstitutionStep_parallel (n : ℕ) (V : Fin (n + 1) → Complex A)
    {R U S S₁ R₁ R₂ O : Complex A}
    (f : R ⊗ U ⟶ S) (g : R ⊗ V (Fin.last n) ⟶ R₁)
    (h : S ⊗ V (Fin.last n) ⟶ S₁) (f₁ : R₁ ⊗ U ⟶ S₁)
    (v : S₁ ⊗ tensorFamily n (fun j => V j.castSucc) ⟶ O)
    (w : R₁ ⊗ tensorFamily n (fun j => V j.castSucc) ⟶ R₂) (f₂ : R₂ ⊗ U ⟶ O)
    (hf : (f ▷ V (Fin.last n)) ≫ h =
      (α_ R U (V (Fin.last n))).hom ≫ tensorSubstitutionStep g f₁)
    (hv : (f₁ ▷ tensorFamily n (fun j => V j.castSucc)) ≫ v =
      (α_ R₁ U (tensorFamily n (fun j => V j.castSucc))).hom ≫ tensorSubstitutionStep w f₂) :
    (f ▷ tensorFamily (n + 1) V) ≫ tensorFamilySubstitutionStep n V h v =
      (α_ R U (tensorFamily (n + 1) V)).hom ≫
        tensorSubstitutionStep (tensorFamilySubstitutionStep n V g w) f₂ := by
  unfold tensorFamilySubstitutionStep
  rw [← whisker_exchange_assoc, tensorSubstitutionStep_parallel f g h f₁ v w f₂ hf hv,
    associator_naturality_right_assoc, tensorSubstitutionStep_last]

end SerrePositivity.EInfinity
