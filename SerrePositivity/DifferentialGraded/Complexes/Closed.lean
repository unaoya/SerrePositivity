module
public import SerrePositivity.DifferentialGraded.Complexes.Braiding
public import SerrePositivity.DifferentialGraded.Complexes.Currying
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-! # 非有界 Ch(A) の閉対称モノイダル構造

右 tensor 転置から Koszul braiding を使って Mathlib の左 tensor 随伴を構成する。
右随伴の対象は既存 linearHomComplex のままである。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable {A : Type u} [CommRing A]

/-- 右 tensor と既存線形 Hom 関手の随伴。 -/
def tensorRightHomAdjunction (P : Complex A) : tensorRight P ⊣ homFunctor P :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun Q T => tensorRightHomEquiv P Q T
      homEquiv_naturality_left_symm := by
        intro Q' Q T g t
        apply (tensorRightHomEquiv P Q' T).injective
        change curryRight (uncurryRight (g ≫ t)) = curryRight ((g ⊗ₘ 𝟙 P) ≫ uncurryRight t)
        rw [curryRight_naturality_source, curryRight_uncurryRight, curryRight_uncurryRight]
      homEquiv_naturality_right := by
        intro Q T T' f g
        exact curryRight_naturality_target f g }

/-- Mathlib の左 tensor を基準とする閉構造。
同じ Hom 複体を右随伴とし、braiding の自然同型を介して転置する。 -/
instance complexClosed (P : Complex A) : Closed P where
  rightAdj := homFunctor P
  adj := (tensorRightHomAdjunction P).ofNatIsoLeft (BraidedCategory.tensorLeftIsoTensorRight P).symm

/-- 任意可換環上の非有界 Ch(A) は閉対称モノイダル圏。 -/
instance complexMonoidalClosed : MonoidalClosed (Complex A) where
  closed := complexClosed

/-- 内部 Hom の対象は既存 linearHomComplex に一致する。 -/
lemma internalHom_eq (P T : Complex A) :
    (ihom P).obj T = homComplex A P T := rfl

/-- 左 tensor の Hom 同値。Mathlib に登録した閉構造そのものを用いる。 -/
abbrev tensorHomEquiv (P Q T : Complex A) : (P ⊗ Q ⟶ T) ≃ (Q ⟶ homComplex A P T) :=
  (ihom.adjunction P).homEquiv Q T
/-- 登録した左tensor転置は、signed braiding の後の右tensor転置に一致する。 -/
lemma tensorHomEquiv_curryRight (P Q T : Complex A) (f : P ⊗ Q ⟶ T) :
    tensorHomEquiv P Q T f = curryRight ((signedSwap Q P).hom ≫ f) := by
  change ((tensorRightHomAdjunction P).ofNatIsoLeft
    (BraidedCategory.tensorLeftIsoTensorRight P).symm).homEquiv Q T f = _
  rw [Adjunction.homEquiv_ofNatIsoLeft_apply]
  change (tensorRightHomAdjunction P).homEquiv Q T ((β_ P Q).inv ≫ f) = _
  rw [← SymmetricCategory.braiding_swap_eq_inv_braiding]
  simp only [tensorRightHomAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- 左tensor転置の評価公式。全整数次数で Koszul 符号を明示する。 -/
lemma tensorHomEquiv_component (P Q T : Complex A) (f : P ⊗ Q ⟶ T)
    (q i n : ℤ) (hn : i + q = n) (x : Q.X q) (y : P.X i) :
    ((tensorHomEquiv P Q T f).f q x).v i n hn y =
      (q * i).negOnePow • f.f n (HomologicalComplex.ιTensorObj P Q i q n hn (y ⊗ₜ[A] x)) := by
  rw [tensorHomEquiv_curryRight]
  change (curryComponent ((signedSwap Q P).hom ≫ f) q x).v i n hn y = _
  rw [curryComponent_apply]
  change f.f n ((signedSwap Q P).hom.f n
    (HomologicalComplex.ιTensorObj Q P q i n (by omega) (x ⊗ₜ[A] y))) = _
  rw [signedSwap_apply]
  simp only [Units.smul_def, map_zsmul]

/-- 左tensor転置は Q 変数で自然。 -/
lemma tensorHomEquiv_naturality_source (P : Complex A) {Q Q' T : Complex A}
    (g : Q' ⟶ Q) (f : P ⊗ Q ⟶ T) :
    tensorHomEquiv P Q' T ((P ◁ g) ≫ f) = g ≫ tensorHomEquiv P Q T f :=
  (ihom.adjunction P).homEquiv_naturality_left g f

/-- 左tensor転置は T 変数で自然。 -/
lemma tensorHomEquiv_naturality_target (P : Complex A) {Q T T' : Complex A}
    (f : P ⊗ Q ⟶ T) (g : T ⟶ T') :
    tensorHomEquiv P Q T' (f ≫ g) = tensorHomEquiv P Q T f ≫ homPostcompose P g :=
  (ihom.adjunction P).homEquiv_naturality_right f g

/-- 左tensor転置は P 変数で反変に自然。 -/
lemma tensorHomEquiv_naturality_domain {P P' Q T : Complex A}
    (g : P' ⟶ P) (f : P ⊗ Q ⟶ T) :
    tensorHomEquiv P' Q T ((g ▷ Q) ≫ f) = tensorHomEquiv P Q T f ≫ homPrecompose g T := by
  rw [tensorHomEquiv_curryRight, tensorHomEquiv_curryRight]
  change curryRight ((β_ Q P').hom ≫ g ▷ Q ≫ f) = _
  rw [← BraidedCategory.braiding_naturality_right_assoc]
  change curryRight ((𝟙 Q ⊗ₘ g) ≫ (signedSwap Q P).hom ≫ f) = _
  rw [curryRight_naturality_domain]
/-- 左tensorの逆転置は、符号付き交換の後の右tensor逆転置。 -/
lemma tensorHomEquiv_uncurryRight (P Q T : Complex A) (t : Q ⟶ homComplex A P T) :
    (tensorHomEquiv P Q T).symm t = (signedSwap P Q).hom ≫ uncurryRight t := by
  change (((tensorRightHomAdjunction P).ofNatIsoLeft
    (BraidedCategory.tensorLeftIsoTensorRight P).symm).homEquiv Q T).symm t = _
  rw [Adjunction.homEquiv_ofNatIsoLeft_symm_apply]
  simp only [tensorRightHomAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- 左tensor逆転置の全次数での成分公式。 -/
lemma tensorHomEquiv_symm_component (P Q T : Complex A) (t : Q ⟶ homComplex A P T)
    (i q n : ℤ) (hn : i + q = n) (y : P.X i) (x : Q.X q) :
    ((tensorHomEquiv P Q T).symm t).f n
      (HomologicalComplex.ιTensorObj P Q i q n hn (y ⊗ₜ[A] x)) =
      (i * q).negOnePow • (t.f q x).v i n hn y := by
  rw [tensorHomEquiv_uncurryRight]
  change (uncurryRight t).f n ((signedSwap P Q).hom.f n
    (HomologicalComplex.ιTensorObj P Q i q n hn (y ⊗ₜ[A] x))) = _
  rw [signedSwap_apply]
  simp only [Units.smul_def, map_zsmul]
  rw [uncurryRight_apply]

/-- Mathlib の evaluation は標準 Hom 評価に Koszul 符号を付けた射。 -/
lemma evaluation_component (P T : Complex A) (i q n : ℤ) (hn : i + q = n)
    (y : P.X i) (f : Homogeneous P T q) :
    ((ihom.ev P).app T).f n
      (HomologicalComplex.ιTensorObj P (homComplex A P T) i q n hn (y ⊗ₜ[A] f)) =
      (i * q).negOnePow • f.v i n hn y := by
  change ((ihom.adjunction P).counit.app T).f n
    (HomologicalComplex.ιTensorObj P (homComplex A P T) i q n hn (y ⊗ₜ[A] f)) = _
  rw [← (ihom.adjunction P).homEquiv_symm_id]
  change ((tensorHomEquiv P (homComplex A P T) T).symm (𝟙 _)).f n _ = _
  rw [tensorHomEquiv_symm_component]
  rfl
end SerrePositivity.DifferentialGraded
