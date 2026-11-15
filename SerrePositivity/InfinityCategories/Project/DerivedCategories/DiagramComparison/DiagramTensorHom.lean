module
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-!
概要：図式のテンソルからの射を、自然性条件を持つ点ごとの Hom 射の族と同定する。
方針：既存の閉テンソル随伴の始域・標的自然性を使い、転置の前後で同じ条件を保つ。
規約：点ごとの射の族だけでなく、添字の全射との両立を型に含める。
使われ方：HA 1.2.4、G10 の図式 Hom 複体と全単体テンソル Hom の接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable {A : Type u} [CommRing A] {J : Type v} [Category.{w} J]
variable (P Q : J ⥤ Complex A) (T : Complex A)

/-- 添字の全射に対して前合成と後合成が一致する、点ごとの転置の族。 -/
def DiagramHomFamily :=
  {g : ∀ j, T ⟶ homComplex A (P.obj j) (Q.obj j) //
    ∀ ⦃i j⦄ (f : i ⟶ j),
      g j ≫ homPrecompose (P.map f) (Q.obj j) =
        g i ≫ homPostcompose (P.obj i) (Q.map f)}

/-- 図式のテンソル射を、同じ自然性条件つきの Hom 射の族へ転置する。 -/
def diagramTensorHomEquiv :
    (P ⊗ (Functor.const J).obj T ⟶ Q) ≃ DiagramHomFamily P Q T where
  toFun f := ⟨fun j => tensorHomEquiv (P.obj j) T (Q.obj j) (f.app j), by
    intro i j t
    have hn := f.naturality t
    change (P.map t ⊗ₘ 𝟙 T) ≫ f.app j = f.app i ≫ Q.map t at hn
    rw [tensorHom_id] at hn
    have h := congrArg (tensorHomEquiv (P.obj i) T (Q.obj j)) hn
    rw [tensorHomEquiv_naturality_domain, tensorHomEquiv_naturality_target] at h
    exact h⟩
  invFun g :=
    { app := fun j => (tensorHomEquiv (P.obj j) T (Q.obj j)).symm (g.val j)
      naturality := by
        intro i j t
        change (P.map t ⊗ₘ 𝟙 T) ≫ _ = _
        rw [tensorHom_id]
        apply (tensorHomEquiv (P.obj i) T (Q.obj j)).injective
        rw [tensorHomEquiv_naturality_domain, tensorHomEquiv_naturality_target]
        simpa only [Equiv.apply_symm_apply] using g.property t }
  left_inv f := by
    apply NatTrans.ext
    funext j
    exact (tensorHomEquiv (P.obj j) T (Q.obj j)).symm_apply_apply (f.app j)
  right_inv g := by
    apply Subtype.ext
    funext j
    exact (tensorHomEquiv (P.obj j) T (Q.obj j)).apply_symm_apply (g.val j)

/-- 転置はパラメータ複体の全射による前合成と可換。 -/
theorem diagramTensorHomEquiv_precomp {T' : Complex A} (g : T' ⟶ T)
    (f : P ⊗ (Functor.const J).obj T ⟶ Q) (j : J) :
    (diagramTensorHomEquiv P Q T' ((P ◁ (Functor.const J).map g) ≫ f)).val j =
      g ≫ (diagramTensorHomEquiv P Q T f).val j :=
  tensorHomEquiv_naturality_source (P.obj j) g (f.app j)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
