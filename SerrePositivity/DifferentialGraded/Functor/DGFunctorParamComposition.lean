module
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorParamNaturality
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation

/-! # dg 関手の全次数パラメータ自然変換の縦合成
概要：元のパラメータと全対象の Hom 合成を保って全次数自然変換を合成する。
方針：三重 tensor の純テンソルと斉次結合律で自然性の二つの符号を消去する。
規約：任意の標的 dg 圏に適用する。使われ方：Hom end の dg 合成への持ち上げ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex
open SerrePositivity.DifferentialGraded

private lemma forward_smul_left {A : Type u} [CommRing A] {E : Type w} [DGCategory A E]
    {x y z : E} {p q n : ℤ} (f : GradedHom A x y p) (g : GradedHom A y z q)
    (hn : p + q = n) (c : ℤˣ) : forward A (c • f) g hn = c • forward A f g hn := by
  simp only [forward, Units.smul_def, ← TensorProduct.smul_tmul', map_zsmul]

private lemma forward_smul_right {A : Type u} [CommRing A] {E : Type w} [DGCategory A E]
    {x y z : E} {p q n : ℤ} (f : GradedHom A x y p) (g : GradedHom A y z q)
    (hn : p + q = n) (c : ℤˣ) : forward A f (c • g) hn = c • forward A f g hn := by
  simp only [forward, Units.smul_def, TensorProduct.tmul_smul, map_zsmul]

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (E : Type w) [DGCategory A E]

/-- 元の全対象での豊穣合成を、同じ二つのパラメータに保つ chain map。 -/
def dgFunctorFamilyComposeApp {K L : Complex A} {M N P : DGFunctor A D E}
    (a : ∀ x : D, K ⟶ homObject A E (M.obj x) (N.obj x))
    (b : ∀ x : D, L ⟶ homObject A E (N.obj x) (P.obj x)) (x : D) :
    K ⊗ L ⟶ homObject A E (M.obj x) (P.obj x) :=
  (a x ⊗ₘ b x) ≫ eComp (Complex A) _ _ _

/-- 元の二つの斉次パラメータの像は、同じ斉次 Hom の豊穣合成。 -/
lemma dgFunctorFamilyComposeApp_apply {K L : Complex A} {M N P : DGFunctor A D E}
    (a : ∀ x : D, K ⟶ homObject A E (M.obj x) (N.obj x))
    (b : ∀ x : D, L ⟶ homObject A E (N.obj x) (P.obj x)) (x : D)
    {k l n : ℤ} (hn : k + l = n) (t : K.X k) (s : L.X l) :
    (dgFunctorFamilyComposeApp A D E a b x).f n (ιTensorObj K L k l n hn (t ⊗ₜ[A] s)) =
      forward A ((a x).f k t) ((b x).f l s) hn := by
  change (eComp (Complex A) _ _ _).f n
    ((a x ⊗ₘ b x).f n (ιTensorObj K L k l n hn (t ⊗ₜ[A] s))) = _
  rw [tensorMap_apply]
  rfl

/-- 二つの元の自然性は、同じ tensor パラメータの全次数自然性を与える。 -/
lemma dgFunctorFamilyComposeApp_naturality {K L : Complex A} {M N P : DGFunctor A D E}
    (a : ∀ x : D, K ⟶ homObject A E (M.obj x) (N.obj x))
    (b : ∀ x : D, L ⟶ homObject A E (N.obj x) (P.obj x))
    (hAn : ∀ x y : D, (β_ K (x ⟶[Complex A] y)).hom ≫ (M.map x y ⊗ₘ a y) ≫
      eComp (Complex A) _ _ _ = (a x ⊗ₘ N.map x y) ≫ eComp (Complex A) _ _ _)
    (hBn : ∀ x y : D, (β_ L (x ⟶[Complex A] y)).hom ≫ (N.map x y ⊗ₘ b y) ≫
      eComp (Complex A) _ _ _ = (b x ⊗ₘ P.map x y) ≫ eComp (Complex A) _ _ _)
    (x y : D) :
    (β_ (K ⊗ L) (x ⟶[Complex A] y)).hom ≫
      (M.map x y ⊗ₘ dgFunctorFamilyComposeApp A D E a b y) ≫ eComp (Complex A) _ _ _ =
    (dgFunctorFamilyComposeApp A D E a b x ⊗ₘ P.map x y) ≫ eComp (Complex A) _ _ _ := by
  apply triple_ext
  intro k l p n hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro t s f
  change (eComp (Complex A) _ _ _).f n
      ((M.map x y ⊗ₘ dgFunctorFamilyComposeApp A D E a b y).f n
        ((signedSwap (K ⊗ L) (x ⟶[Complex A] y)).hom.f n
          (ιTensorObj (K ⊗ L) (x ⟶[Complex A] y) (k + l) p n hn
            (ιTensorObj K L k l (k + l) rfl (t ⊗ₜ[A] s) ⊗ₜ[A] f)))) =
    (eComp (Complex A) _ _ _).f n
      ((dgFunctorFamilyComposeApp A D E a b x ⊗ₘ P.map x y).f n
        (ιTensorObj (K ⊗ L) (x ⟶[Complex A] y) (k + l) p n hn
          (ιTensorObj K L k l (k + l) rfl (t ⊗ₜ[A] s) ⊗ₜ[A] f)))
  rw [signedSwap_apply]
  simp only [Units.smul_def, map_zsmul]
  rw [tensorMap_apply, tensorMap_apply, dgFunctorFamilyComposeApp_apply,
    dgFunctorFamilyComposeApp_apply]
  change ((k + l) * p).negOnePow •
    forward A ((M.map x y).f p f)
      (forward A ((a y).f k t) ((b y).f l s) rfl) (by omega) =
    forward A (forward A ((a x).f k t) ((b x).f l s) rfl)
      ((P.map x y).f p f) hn
  have ha := dgFunctorFamilyNaturality_apply A D E a hAn t f (n := p + k) (by omega)
  have hb := dgFunctorFamilyNaturality_apply A D E b hBn s f (n := p + l) (by omega)
  have ha' := congrArg (fun z => (k * p).negOnePow • z) ha
  have hb' := congrArg (fun z => (l * p).negOnePow • z) hb
  simp only [smul_smul, Int.units_mul_self, one_smul] at ha' hb'
  rw [← forward_assoc_of_sum A _ _ _ (a := p + k) (b := k + l) rfl rfl (by omega),
    ha', forward_smul_left,
    forward_assoc_of_sum A _ _ _ (a := p + k) (b := p + l) (by omega) rfl (by omega),
    hb', forward_smul_right,
    ← forward_assoc_of_sum A _ _ _ (a := k + l) (b := p + l) rfl (by omega) hn]
  simp only [smul_smul]
  rw [← Int.negOnePow_add, ← add_mul, Int.units_mul_self, one_smul]

/-- 全次数自然変換の元の tensor パラメータによる縦合成。 -/
def dgFunctorParamCompose {K L : Complex A} {M N P : DGFunctor A D E}
    (a : DGFunctorParamTrans A D E K M N) (b : DGFunctorParamTrans A D E L N P) :
    DGFunctorParamTrans A D E (K ⊗ L) M P where
  app := dgFunctorFamilyComposeApp A D E a.app b.app
  naturality := dgFunctorFamilyComposeApp_naturality A D E a.app b.app a.naturality b.naturality

end SerrePositivity.KST.SConstruction
