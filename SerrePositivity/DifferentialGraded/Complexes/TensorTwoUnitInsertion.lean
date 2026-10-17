module
public import SerrePositivity.DifferentialGraded.Complexes.TensorUnitInsertion

/-! # 異なる左右単位を挿入したtensorと後方作用

## 概要
異なる左右単位を挿入したtensorと後方作用。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。dg加群の導来作用・準同値比較の基盤。任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable {A : Type u} [CommRing A]

lemma tensorSandwich_append_distinct (E H₁ H₂ P : Complex A)
    (e₁ : 𝟙_ (Complex A) ⟶ H₁) (e₂ : 𝟙_ (Complex A) ⟶ H₂)
    (f : H₂ ⊗ P ⟶ P) (hu : (λ_ P).inv ≫ e₂ ▷ P ≫ f = 𝟙 P) :
    (((λ_ E).inv ≫ (e₁ ⊗ₘ ((ρ_ E).inv ≫ (𝟙 E ⊗ₘ e₂)))) ▷ P) ≫
      (α_ H₁ (E ⊗ H₂) P).hom ≫ H₁ ◁ ((α_ E H₂ P).hom ≫ E ◁ f) =
    (λ_ (E ⊗ P)).inv ≫ e₁ ▷ (E ⊗ P) := by
  have hunit : (λ_ E).inv ▷ P ≫ (α_ (𝟙_ (Complex A)) E P).hom = (λ_ (E ⊗ P)).inv := by
    monoidal
  simp only [tensorHom_def, comp_whiskerRight, id_whiskerRight, Category.id_comp, Category.assoc]
  rw [associator_naturality_middle_assoc, associator_naturality_left_assoc]
  rw [← whiskerLeft_comp, tensorMiddle_left_unit E H₂ P e₂ f hu,
    whiskerLeft_id, Category.comp_id]
  simpa only [Category.assoc] using congrArg (fun t => t ≫ e₁ ▷ (E ⊗ P)) hunit

end SerrePositivity.DifferentialGraded
