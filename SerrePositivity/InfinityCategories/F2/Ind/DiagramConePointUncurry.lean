module

public import SerrePositivity.InfinityCategories.F2.Ind.DiagramConePointRestriction

/-!
概要：元の全錐 comma の点制限は、その同じ全錐の点への制限を回収する。
方針：終点の二つの表示変更は全錐を変えないことを確認し、実 slice 制限へ戻す。
規約：全パラメーター・全次数の等式。使われ方：始点余錐と元の円柱の全境界の一致。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 固定図式の表示変更による実 comma の移送は、元の全錐を変えない。 -/
lemma coneCommaTransport_uncurry {B K X T : SSet.{u}} (δ : B ⟶ X)
    {p q : K ⟶ X} (h : p = q) (a : T ⟶ pullback δ (sliceOverProjection p)) :
    sliceOverUncurry (a ≫ eqToHom
      (congrArg (fun r : K ⟶ X => pullback δ (sliceOverProjection r)) h) ≫
        pullback.snd δ (sliceOverProjection q)) =
      sliceOverUncurry (a ≫ pullback.snd δ (sliceOverProjection p)) := by
  cases h
  simp only [eqToHom_refl, Category.id_comp]

/-- 点制限の表示を全て戻すと、同じ元の全錐の指定点制限になる。 -/
lemma diagramConePointRestriction_uncurry (κ : Cardinal.{u}) {K C : SSet.{u}}
    [Quasicategory C] (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ IndInfinity κ C)
    (k : K _⦋0⦌) {T : SSet.{u + 1}}
    (H : T ⟶ pullback (indYoneda κ C) (sliceOverProjection D)) :
    sliceOverUncurry (H ≫ diagramConePointRestriction κ D k ≫
      pullback.snd (indYoneda κ C) (sliceOverProjection (SSet.yonedaEquiv.symm
        (D.app (Opposite.op ⦋0⦌) (ULift.up k))))) =
      sliceOverUncurry (H ≫ pullback.snd (indYoneda κ C) (sliceOverProjection D) ≫
        sliceOverRestrict D (diagramShapePoint k)) := by
  let i := diagramShapePoint k
  have h₁ := commaTransport_uncurry (indYoneda κ C) (diagramConePoint_value κ D k)
    (H ≫ indConeCommaPointRestriction κ D i)
  have h₂ := coneCommaTransport_uncurry (indYoneda κ C)
    (Equiv.symm_apply_apply SSet.yonedaEquiv (i ≫ D)).symm
    (H ≫ coneCommaRestriction (indYoneda κ C) D i)
  calc
    _ = sliceOverUncurry (H ≫ indConeCommaPointRestriction κ D i ≫
        pullback.snd (indYoneda κ C) (sliceOverProjection
          (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (i ≫ D))))) := by
      simpa only [diagramConePointRestriction, Category.assoc] using h₁
    _ = sliceOverUncurry (H ≫ coneCommaRestriction (indYoneda κ C) D i ≫
        pullback.snd (indYoneda κ C) (sliceOverProjection (i ≫ D))) := by
      simpa only [indConeCommaPointRestriction, indConeCommaPointIso,
        eqToIso.hom, Category.assoc] using h₂
    _ = _ := by rw [coneCommaRestriction_snd]

end SerrePositivity.InfinityCategories.F2.Ind
