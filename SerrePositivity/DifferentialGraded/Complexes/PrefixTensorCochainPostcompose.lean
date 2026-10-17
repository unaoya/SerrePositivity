module
public import SerrePositivity.DifferentialGraded.Complexes.PrefixTensorCochain
public import SerrePositivity.DifferentialGraded.Complexes.TensorCochainComposition
public import SerrePositivity.DifferentialGraded.Complexes.TensorClosedZero

/-! # 前方二因子を保つcochain輸送と後合成

## 概要
前方二因子を保つcochain輸送と後合成。

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
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

lemma prefixTensor_cochain_middle_postcompose (K E P P' Q T V : Complex A) (p : ℤ)
    (f : Cochain P P' p) (m : P' ⊗ Q ⟶ T) (h : K ⊗ (E ⊗ T) ⟶ V) :
    ((tensorRightHom Q (K ⊗ (E ⊗ P)) (K ⊗ (E ⊗ P'))).f p
      ((tensorLeftHom K (E ⊗ P) (E ⊗ P')).f p ((tensorLeftHom E P P').f p f))).comp
      (Cochain.ofHom ((α_ K (E ⊗ P') Q).hom ≫ K ◁ (α_ E P' Q).hom ≫
        K ◁ (E ◁ m) ≫ h)) (add_zero p) =
    ((Cochain.ofHom ((α_ K (E ⊗ P) Q).hom ≫ K ◁ (α_ E P Q).hom)).comp
      ((tensorLeftHom K (E ⊗ (P ⊗ Q)) (E ⊗ T)).f p
        ((tensorLeftHom E (P ⊗ Q) T).f p
          (((tensorRightHom Q P P').f p f).comp (Cochain.ofHom m) (add_zero p))))
      (zero_add p)).comp (Cochain.ofHom h) (add_zero p) := by
  rw [tensorLeftHom_cochain_comp, tensorLeftHom_ofHom,
    tensorLeftHom_cochain_comp, tensorLeftHom_ofHom]
  have hp := congrArg (fun c : Cochain ((K ⊗ (E ⊗ P)) ⊗ Q)
      (K ⊗ (E ⊗ (P' ⊗ Q))) p =>
    c.comp (Cochain.ofHom (K ◁ (E ◁ m) ≫ h)) (add_zero p))
    (prefixTensor_cochain_middle K E P P' Q p f)
  simp only [Cochain.ofHom_comp,
    ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← Cochain.comp_assoc_of_second_is_zero_cochain] at hp ⊢
  exact hp

lemma prefixTensor_cochain_right_postcompose (K E P Q Q' T V : Complex A) (p : ℤ)
    (f : Cochain Q Q' p) (m : P ⊗ Q' ⟶ T) (h : K ⊗ (E ⊗ T) ⟶ V) :
    ((tensorLeftHom (K ⊗ (E ⊗ P)) Q Q').f p f).comp
      (Cochain.ofHom ((α_ K (E ⊗ P) Q').hom ≫ K ◁ (α_ E P Q').hom ≫
        K ◁ (E ◁ m) ≫ h)) (add_zero p) =
    ((Cochain.ofHom ((α_ K (E ⊗ P) Q).hom ≫ K ◁ (α_ E P Q).hom)).comp
      ((tensorLeftHom K (E ⊗ (P ⊗ Q)) (E ⊗ T)).f p
        ((tensorLeftHom E (P ⊗ Q) T).f p
          (((tensorLeftHom P Q Q').f p f).comp (Cochain.ofHom m) (add_zero p))))
      (zero_add p)).comp (Cochain.ofHom h) (add_zero p) := by
  rw [tensorLeftHom_cochain_comp, tensorLeftHom_ofHom,
    tensorLeftHom_cochain_comp, tensorLeftHom_ofHom]
  have hp := congrArg (fun c : Cochain ((K ⊗ (E ⊗ P)) ⊗ Q)
      (K ⊗ (E ⊗ (P ⊗ Q'))) p =>
    c.comp (Cochain.ofHom (K ◁ (E ◁ m) ≫ h)) (add_zero p))
    (prefixTensor_cochain_right K E P Q Q' p f)
  simp only [Cochain.ofHom_comp,
    ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← Cochain.comp_assoc_of_second_is_zero_cochain] at hp ⊢
  exact hp

end SerrePositivity.DifferentialGraded
