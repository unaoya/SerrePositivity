module
public import SerrePositivity.KST.SConstruction.DGFunctorHorizontalComposition
public import SerrePositivity.DifferentialGraded.Functor.Components
public import SerrePositivity.DifferentialGraded.Category.TensorElements

/-! # 横合成の元の全斉次パラメータと対象評価
概要：横合成の chain map を全次数の元で計算し、各対象の元の合成を回収する。
方針：全対象評価の chain map 等号を純テンソルで評価する。
規約：二つの元の次数を保持する。使われ方：tensor dg 合成保存の符号判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded

/-- 全次数 Hom end の評価は、元の同じ斉次合成を保つ。 -/
lemma dgFunctorHomπ_forward (A : Type u) [CommRing A]
    (D : Type v) [DGCategory A D] [Small.{u} D] (E : Type w) [DGCategory A E]
    {M N P : DGFunctor A D E} {p q n : ℤ} (x : D)
    (a : GradedHom A M N p) (b : GradedHom A N P q) (hn : p + q = n) :
    (dgFunctorHomπ A D E M P x).f n (forward A a b hn) =
      forward A ((dgFunctorHomπ A D E M N x).f p a)
        ((dgFunctorHomπ A D E N P x).f q b) hn :=
  DGFunctor.map_forward A (dgFunctorEvaluationDG A D E x) a b hn

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (B : Type t) [DGCategory A B]
  {F₀ F₁ : DGFunctor A D E} {G₀ G₁ : DGFunctor A E B}

/-- 二つの元の斉次自然変換による横合成の元。 -/
def dgFunctorHorizontalElement {p q n : ℤ}
    (a : GradedHom A F₀ F₁ p) (b : GradedHom A G₀ G₁ q) (hn : p + q = n) :
    GradedHom A (F₀.comp G₀) (F₁.comp G₁) n :=
  (dgFunctorHorizontal A D E B F₀ F₁ G₀ G₁).f n
    (ιTensorObj (dgFunctorHom A D E F₀ F₁) (dgFunctorHom A E B G₀ G₁)
      p q n hn (a ⊗ₜ[A] b))

/-- 横合成の元は各対象で、元の後合成の像と次の元の評価の豊穣合成になる。 -/
lemma dgFunctorHorizontalElement_π {p q n : ℤ}
    (a : GradedHom A F₀ F₁ p) (b : GradedHom A G₀ G₁ q) (hn : p + q = n) (x : D) :
    (dgFunctorHomπ A D B (F₀.comp G₀) (F₁.comp G₁) x).f n
        (dgFunctorHorizontalElement A D E B a b hn) =
      forward A ((G₀.map (F₀.obj x) (F₁.obj x)).f p
        ((dgFunctorHomπ A D E F₀ F₁ x).f p a))
        ((dgFunctorHomπ A E B G₀ G₁ (F₁.obj x)).f q b) hn := by
  have h := congrArg (fun k => k.f n
    (ιTensorObj (dgFunctorHom A D E F₀ F₁) (dgFunctorHom A E B G₀ G₁)
      p q n hn (a ⊗ₜ[A] b))) (dgFunctorHorizontal_π A D E B F₀ F₁ G₀ G₁ x)
  change (dgFunctorHomπ A D B (F₀.comp G₀) (F₁.comp G₁) x).f n
      (dgFunctorHorizontalElement A D E B a b hn) =
    (eComp (Complex A) _ _ _).f n
      (((dgFunctorHomπ A D E F₀ F₁ x ≫ G₀.map (F₀.obj x) (F₁.obj x)) ⊗ₘ
        dgFunctorHomπ A E B G₀ G₁ (F₁.obj x)).f n
        (ιTensorObj (dgFunctorHom A D E F₀ F₁) (dgFunctorHom A E B G₀ G₁)
          p q n hn (a ⊗ₜ[A] b))) at h
  rw [tensorMap_apply] at h
  exact h

end SerrePositivity.KST.SConstruction
