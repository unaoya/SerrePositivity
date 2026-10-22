module
public import SerrePositivity.InfinityCategories.Core.ConeFamily
public import SerrePositivity.InfinityCategories.Core.FunctorCompositionEvaluation

/-!
概要：内部 Hom の curry の頂点と評価を元の全射の制限で計算する。
方針：同じ実図式の貼り合わせ・全パラメーターの評価・普遍的な切断比較を使う。
規約：一般安定性を先取りしない。使われ方：HA 1.4.2.15 の実 θ の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

lemma curry_vertex_evaluation {K P X : SSet.{u}} (H : K ⊗ P ⟶ X) (v : P _⦋0⦌) :
    (curry H).app (Opposite.op ⦋0⦌) v =
      functorVertex (lift (𝟙 K) (SSet.const v) ≫ H) := by
  apply SSet.yonedaEquiv.symm.injective
  rw [← SSet.yonedaEquiv_symm_comp, ← curry_natural_left]
  apply uncurry_injective
  rw [uncurry_curry, uncurry_yoneda_functorVertex, SSet.yonedaEquiv_symm_zero]
  rfl

lemma curry_evaluation_vertex {K P X : SSet.{u}} (H : K ⊗ P ⟶ X) (v : K _⦋0⦌) :
    curry H ≫ evaluateFunctorAt v = lift (SSet.const v) (𝟙 P) ≫ H := by
  have h := curry_evaluateFunctorAt_unitHomEquiv H ((SSet.unitHomEquiv K).symm v)
  rw [Equiv.apply_symm_apply] at h
  calc
    _ = (λ_ P).inv ≫ (((SSet.unitHomEquiv K).symm v) ▷ P) ≫ H := h
    _ = _ := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro p
      rfl

end SerrePositivity.InfinityCategories
