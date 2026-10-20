module
public import SerrePositivity.KST.SConstruction.DGExtensionParameterPullback
public import SerrePositivity.KST.SConstruction.DGParameterUniversal
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGInputHom

/-! # 任意パラメータ作用の元の入力 Hom を通る因子化
概要：任意 K のラベル付き作用は、元の入力 Hom の作用への同じ前合成である。
方針：元の Hom end の普遍性と、作用のパラメータ引き戻しとの可換性を合成する。
規約：各ラベルの全 Hom を保持する。使われ方：高次入力の単位・合成の検証。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]
  {F G : DGFunctor A D E}

/-- 任意 K の作用は、元の入力 Hom への表示射と同じ普遍作用の合成である。 -/
lemma presentedPerfectDGInputHom_factorization {K : Complex A}
    (τ : DGFunctorParamTrans A D E K F G) (X : PresentedPerfectDGObject A D) :
    (dgFunctorHomEquiv A D E K F G).symm τ ≫ presentedPerfectDGInputHom A D E F G X =
      (presentedPerfectDGParameter A D E τ).app X := by
  have h := congrArg (fun σ => (presentedPerfectDGParameter A D E σ).app X)
    (dgParameterUniversal_pullback A D E F G τ)
  rw [presentedPerfectDGParameter_pullback] at h
  exact h

/-- 入力 Hom の作用への任意 chain map の前合成は、そのパラメータ自然変換の作用。 -/
lemma presentedPerfectDGInputHom_precompose {K : Complex A}
    (a : K ⟶ dgFunctorHom A D E F G) (X : PresentedPerfectDGObject A D) :
    a ≫ presentedPerfectDGInputHom A D E F G X =
      (presentedPerfectDGParameter A D E (dgFunctorHomEquiv A D E K F G a)).app X := by
  simpa only [Equiv.symm_apply_apply] using presentedPerfectDGInputHom_factorization A D E
    (dgFunctorHomEquiv A D E K F G a) X

end SerrePositivity.KST.SConstruction
