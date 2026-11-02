module
public import SerrePositivity.KST.SConstruction.DGFunctorHorizontalElements
public import SerrePositivity.KST.SConstruction.DGFunctorHomElements
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorCoherence

/-! # 横合成の元の全斉次成分の外側結合則
概要：三つの斉次自然変換の横合成を、元の関手の結合の等号に沿って比較する。
方針：全対象評価を保つ移送を使い、標的の dg 合成の結合律へ戻す。
規約：元の三つの次数と対象作用を保持する。使われ方：単体的入力の厳密合成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t s
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded

private lemma triplePairing_assoc {A : Type u} [CommRing A]
    {P Q R U V L Z : Complex A} (f : P ⊗ Q ⟶ U) (g : U ⊗ R ⟶ L) (t : L ⟶ Z)
    (h : Q ⊗ R ⟶ V) (k : P ⊗ V ⟶ Z)
    (hc : ∀ (p q r n : ℤ) (hn : p + q + r = n)
      (a : P.X p) (b : Q.X q) (c : R.X r),
      t.f n (g.f n (ιTensorObj U R (p + q) r n hn
        (f.f (p + q) (ιTensorObj P Q p q (p + q) rfl (a ⊗ₜ[A] b)) ⊗ₜ[A] c))) =
      k.f n (ιTensorObj P V p (q + r) n (by omega)
        (a ⊗ₜ[A] h.f (q + r) (ιTensorObj Q R q r (q + r) rfl (b ⊗ₜ[A] c))))) :
    (f ▷ R) ≫ g ≫ t = (α_ P Q R).hom ≫ P ◁ h ≫ k := by
  apply triple_ext
  intro p q r n hn
  simp only [HomologicalComplex.comp_f]
  rw [ι_whiskerRight_assoc, ι_associator_assoc, ι_whiskerLeft_assoc]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro a b c
  exact hc p q r n hn a b c

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (B : Type t) [DGCategory A B] [Small.{u} B] (T : Type s) [DGCategory A T]

/-- 全斉次元の横合成は、元の dg 関手の結合の等号に沿って結合的。 -/
lemma dgFunctorHorizontalElement_assoc
    {F₀ F₁ : DGFunctor A D E} {G₀ G₁ : DGFunctor A E B} {H₀ H₁ : DGFunctor A B T}
    {p q r n : ℤ} (a : GradedHom A F₀ F₁ p) (b : GradedHom A G₀ G₁ q)
    (c : GradedHom A H₀ H₁ r) (hn : (p + q) + r = n) :
    (dgFunctorHomTransport A D T (strictDGFunctor_comp_assoc F₀ G₀ H₀)
        (strictDGFunctor_comp_assoc F₁ G₁ H₁)).f n
      (dgFunctorHorizontalElement A D B T (dgFunctorHorizontalElement A D E B a b rfl)
        c hn) =
      dgFunctorHorizontalElement A D E T a (dgFunctorHorizontalElement A E B T b c rfl)
        (by omega) := by
  apply dgFunctorHomElement_ext A D T
  intro x
  rw [dgFunctorHomTransport_apply_π]
  simp only [eqToHom_refl]
  simp only [dgFunctorHorizontalElement_π, DGFunctor.map_forward]
  exact forward_assoc A _ _ _ hn

/-- 全パラメータの横合成は、元の関手の結合と tensor の結合に沿って結合的。 -/
lemma dgFunctorHorizontal_assoc
    (F₀ F₁ : DGFunctor A D E) (G₀ G₁ : DGFunctor A E B) (H₀ H₁ : DGFunctor A B T) :
    dgFunctorHorizontal A D E B F₀ F₁ G₀ G₁ ▷ dgFunctorHom A B T H₀ H₁ ≫
        dgFunctorHorizontal A D B T (F₀.comp G₀) (F₁.comp G₁) H₀ H₁ ≫
        dgFunctorHomTransport A D T (strictDGFunctor_comp_assoc F₀ G₀ H₀)
          (strictDGFunctor_comp_assoc F₁ G₁ H₁) =
      (α_ (dgFunctorHom A D E F₀ F₁) (dgFunctorHom A E B G₀ G₁)
        (dgFunctorHom A B T H₀ H₁)).hom ≫
        dgFunctorHom A D E F₀ F₁ ◁ dgFunctorHorizontal A E B T G₀ G₁ H₀ H₁ ≫
          dgFunctorHorizontal A D E T F₀ F₁ (G₀.comp H₀) (G₁.comp H₁) := by
  exact triplePairing_assoc _ _ _ _ _ (fun _ _ _ _ hn a b c =>
    dgFunctorHorizontalElement_assoc A D E B T a b c hn)

end SerrePositivity.KST.SConstruction
