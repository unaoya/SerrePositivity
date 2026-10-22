module

public import SerrePositivity.InfinityCategories.HomotopyLimits.UniverseTwistedArrow
public import SerrePositivity.InfinityCategories.HomotopyLimits.UniverseEdgewiseBoundary

/-!
概要：元の全 twisted arrow の宇宙同型は、元の始点・終点の全射影を厳密に保つ。
方針：同じ重みの両包含の比較を、元の全単体の Yoneda 射へ適用する。
規約：全パラメータの射影正方形を保持する。
使われ方：共同 Hom 分類図式と全 Yoneda 関手の宇宙比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の twisted arrow の両端の底を、持ち上げた元の圏の両端の底へ比較する。 -/
def uliftTwistedArrowBaseIso (C : SSet.{u}) :
    (SSet.uliftFunctor.{v, u}).obj (C.op ⊗ C) ≅
      ((SSet.uliftFunctor.{v, u}).obj C).op ⊗ (SSet.uliftFunctor.{v, u}).obj C :=
  uliftTensorIso C.op C ≪≫ tensorIso (uliftOppositeIso C) (Iso.refl _)

/-- 元の全 twisted arrow の宇宙同型は、両端への元の全射影を厳密に保つ。 -/
lemma uliftTwistedArrowIso_projection (C : SSet.{u}) :
    (uliftTwistedArrowIso.{u, v} C).hom ≫
        twistedArrowProjection ((SSet.uliftFunctor.{v, u}).obj C) =
      (SSet.uliftFunctor.{v, u}).map (twistedArrowProjection C) ≫
        (uliftTwistedArrowBaseIso.{u, v} C).hom := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨f⟩
  have hy (g : (Δ[n] : SSet.{u}) ⟶ C) :
      SSet.yonedaEquiv ((uliftStdSimplexIso.{u, v} n).inv ≫
        (SSet.uliftFunctor.{v, u}).map g) = ULift.up (SSet.yonedaEquiv g) := by
    have h := uliftYonedaMap.{u, v} (SSet.yonedaEquiv g)
    rw [Equiv.symm_apply_apply] at h
    exact (congrArg SSet.yonedaEquiv h).trans (Equiv.apply_symm_apply _ _)
  change (SSet.opObjEquiv.symm (SSet.yonedaEquiv
      ((stdSimplex.opIso ⦋n⦌).inv ≫ joinInl _ _ ≫
        ((edgewiseWeightUniverseIso.{u, v} n).inv ≫ (SSet.uliftFunctor.{v, u}).map f))),
    SSet.yonedaEquiv (joinInr _ _ ≫
      ((edgewiseWeightUniverseIso.{u, v} n).inv ≫ (SSet.uliftFunctor.{v, u}).map f))) =
    (ULift.up (SSet.opObjEquiv.symm (SSet.yonedaEquiv
      ((stdSimplex.opIso ⦋n⦌).inv ≫ joinInl _ _ ≫ f))),
    ULift.up (SSet.yonedaEquiv (joinInr _ _ ≫ f)))
  apply Prod.ext
  · change SSet.yonedaEquiv ((stdSimplex.opIso ⦋n⦌).inv ≫ joinInl _ _ ≫
      ((edgewiseWeightUniverseIso.{u, v} n).inv ≫ (SSet.uliftFunctor.{v, u}).map f)) =
      ULift.up (SSet.yonedaEquiv ((stdSimplex.opIso ⦋n⦌).inv ≫ joinInl _ _ ≫ f))
    have he := edgewiseWeightUniverseIso_inv_leftEndpoint.{u, v} n
    simp only [← Category.assoc] at he ⊢
    rw [he, Category.assoc, ← Functor.map_comp]
    exact hy _
  · change SSet.yonedaEquiv (joinInr _ _ ≫
      ((edgewiseWeightUniverseIso.{u, v} n).inv ≫ (SSet.uliftFunctor.{v, u}).map f)) =
      ULift.up (SSet.yonedaEquiv (joinInr _ _ ≫ f))
    rw [← Category.assoc, edgewiseWeightUniverseIso_inv_inr.{u, v} n,
      Category.assoc, ← Functor.map_comp]
    exact hy _

end SerrePositivity.InfinityCategories.HomotopyLimits
