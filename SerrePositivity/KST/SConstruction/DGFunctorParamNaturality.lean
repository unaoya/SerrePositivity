module
public import SerrePositivity.KST.SConstruction.DGFunctorHomUniversal
public import SerrePositivity.DifferentialGraded.Category.Components

/-! # dg 関手のパラメータ自然性の全斉次成分
概要：元の全 Hom 自然性を、任意の斉次パラメータと元の dg 射の式に戻す。
方針：braiding と tensor の純テンソル評価で Koszul 符号を保持する。
規約：閉零射に限定しない。使われ方：Hom end の縦合成の全次数自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (E : Type w) [DGCategory A E]

/-- 全パラメータの元と全次数の元の射についての、符号を保つ自然性。 -/
lemma dgFunctorFamilyNaturality_apply {K : Complex A} {M N : DGFunctor A D E}
    (σ : ∀ x : D, K ⟶ homObject A E (M.obj x) (N.obj x))
    (hσ : ∀ x y : D, (β_ K (x ⟶[Complex A] y)).hom ≫ (M.map x y ⊗ₘ σ y) ≫
      eComp (Complex A) _ _ _ = (σ x ⊗ₘ N.map x y) ≫ eComp (Complex A) _ _ _)
    {x y : D} {k p n : ℤ}
    (t : K.X k) (f : GradedHom A x y p) (hn : k + p = n) :
    (k * p).negOnePow • forward A ((M.map x y).f p f) ((σ y).f k t) (by omega) =
      forward A ((σ x).f k t) ((N.map x y).f p f) hn := by
  have h₀ : (β_ K (x ⟶[Complex A] y)).hom ≫ (M.map x y ⊗ₘ σ y) ≫
      eComp (Complex A) (M.obj x) (M.obj y) (N.obj y) =
    (σ x ⊗ₘ N.map x y) ≫ eComp (Complex A) (M.obj x) (N.obj x) (N.obj y) :=
    hσ x y
  have h := congrArg (fun l => l.f n
    (ιTensorObj K (x ⟶[Complex A] y) k p n hn (t ⊗ₜ[A] f))) h₀
  change (eComp (Complex A) _ _ _).f n
      ((M.map x y ⊗ₘ σ y).f n
        ((signedSwap K (x ⟶[Complex A] y)).hom.f n
          (ιTensorObj K (x ⟶[Complex A] y) k p n hn (t ⊗ₜ[A] f)))) =
    (eComp (Complex A) _ _ _).f n ((σ x ⊗ₘ N.map x y).f n
      (ιTensorObj K (x ⟶[Complex A] y) k p n hn (t ⊗ₜ[A] f))) at h
  rw [signedSwap_apply] at h
  simp only [Units.smul_def, map_zsmul] at h
  rw [tensorMap_apply, tensorMap_apply] at h
  exact h

/-- 元の全次数パラメータ自然変換に斉次成分の判定を適用する。 -/
lemma dgFunctorParamNaturality_apply {K : Complex A} {M N : DGFunctor A D E}
    (τ : DGFunctorParamTrans A D E K M N) {x y : D} {k p n : ℤ}
    (t : K.X k) (f : GradedHom A x y p) (hn : k + p = n) :
    (k * p).negOnePow • forward A ((M.map x y).f p f) ((τ.app y).f k t) (by omega) =
      forward A ((τ.app x).f k t) ((N.map x y).f p f) hn :=
  dgFunctorFamilyNaturality_apply A D E τ.app τ.naturality t f hn

end SerrePositivity.KST.SConstruction
