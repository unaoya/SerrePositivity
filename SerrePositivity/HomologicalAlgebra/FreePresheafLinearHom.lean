module
public import SerrePositivity.HomologicalAlgebra.FreePresheafFunctor
public import Mathlib.CategoryTheory.Linear.FunctorCategory
import all Mathlib.CategoryTheory.Generator.Presheaf
import all SerrePositivity.HomologicalAlgebra.FreePresheafFunctor

/-!
概要：自由表現可能な線形重みからの射を、指定対象での評価に戻す線形 Yoneda 同値。
方針：既存の freeYonedaHomEquiv に加法性とスカラー倍の保存を与える。
規約：前向きの射は恒等射の生成元での評価。図式の射と添字の射の自然性を保つ。
使われ方：HA 1.2.4、G10 の標準単体重みの線形 end の計算。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t r
open CategoryTheory Limits Preadditive Opposite
namespace SerrePositivity.HomologicalAlgebra
variable {R : Type r} [CommRing R]
variable {J : Type u} [Category.{v} J]
variable {C : Type w} [Category.{t} C] [Preadditive C] [Linear R C] [HasCoproducts.{v} C]

/-- 同じ恒等生成元で評価する線形 Yoneda 同値。 -/
def freePresheafHomLinearEquiv (P : C) (j : J) (X : Jᵒᵖ ⥤ C) :
    ((freePresheafFunctor J P).obj j ⟶ X) ≃ₗ[R] (P ⟶ X.obj (op j)) :=
  { Presheaf.freeYonedaHomEquiv with
    map_add' f g := by simp [Presheaf.freeYonedaHomEquiv, comp_add]
    map_smul' a f := by simp [Presheaf.freeYonedaHomEquiv, Linear.comp_smul] }

/-- 指定評価は係数図式の射への後合成と可換。 -/
theorem freePresheafHomLinearEquiv_comp (P : C) (j : J) {X Y : Jᵒᵖ ⥤ C}
    (f : (freePresheafFunctor J P).obj j ⟶ X) (g : X ⟶ Y) :
    freePresheafHomLinearEquiv (R := R) P j Y (f ≫ g) =
      freePresheafHomLinearEquiv (R := R) P j X f ≫ g.app (op j) :=
  Presheaf.freeYonedaHomEquiv_comp f g

/-- 同じ評価は自由重みの添字の射にも自然。 -/
theorem freePresheafHomLinearEquiv_precompose (P : C) {i j : J} (g : i ⟶ j)
    (X : Jᵒᵖ ⥤ C) (f : (freePresheafFunctor J P).obj j ⟶ X) :
    freePresheafHomLinearEquiv (R := R) P i X ((freePresheafFunctor J P).map g ≫ f) =
      freePresheafHomLinearEquiv (R := R) P j X f ≫ X.map g.op := by
  change Sigma.ι (fun _ : i ⟶ i => P) (𝟙 i) ≫
      ((freePresheafFunctor J P).map g).app (op i) ≫ f.app (op i) = _
  have h := congrArg (fun k => Sigma.ι (fun _ : j ⟶ j => P) (𝟙 j) ≫ k) (f.naturality g.op)
  simpa [freePresheafHomLinearEquiv, Presheaf.freeYonedaHomEquiv,
    freePresheafFunctor, copowerFunctor, Category.assoc] using h

end SerrePositivity.HomologicalAlgebra
