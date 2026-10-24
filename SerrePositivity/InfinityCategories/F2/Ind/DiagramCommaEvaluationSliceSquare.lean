module

public import SerrePositivity.InfinityCategories.F2.Ind.DiagramCommaEvaluation
public import SerrePositivity.InfinityCategories.F2.Ind.DiagramCommaSliceFullyFaithful
public import SerrePositivity.InfinityCategories.Core.SliceMap
/-!
概要：元の図式 comma の評価と、終点を揃えた scalar slice 射影の可換性。
方針：指定図式の終点等号で slice を移し、同じ全余錐の uncurry を回収する。
規約：scalar 射影の充満忠実性も保持。使われ方：始点評価後の指定同型の反映。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：固定図式の端点表示を等号で移しても、同じ全余錐を回収する。
方針：図式の等号を消去する。
規約：元の全射と指定値を保持する。
使われ方：指定始点下の実 comma の相対反映。 -/
lemma sliceOverUncurry_endpointTransport {T K X : SSet.{u}}
    {r s : K ⟶ X} (h : r = s) (a : T ⟶ sliceOver r) :
    sliceOverUncurry (a ≫ eqToHom (congrArg sliceOver h)) = sliceOverUncurry a := by
  subst s
  simp only [eqToHom_refl, Category.comp_id]
/-- 概要：同じ実 comma の第二射影を、等しい指定図式の slice へ移す。
方針：第二射影と等号による輸送を合成する。
規約：元の全射と指定値を保持する。
使われ方：指定始点下の実 comma の相対反映。 -/
def commaSliceEndpointProjection {C K X : SSet.{u}} (δ : C ⟶ X)
    {r s : K ⟶ X} (h : r = s) : pullback δ (sliceOverProjection r) ⟶ sliceOver s :=
  pullback.snd δ (sliceOverProjection r) ≫ eqToHom (congrArg sliceOver h)
/-- 概要：固定図式の表示を変えても、同じ第二射影は充満忠実。
方針：等号を消去して元の引き戻し射影へ戻す。
規約：元の全射と指定値を保持する。
使われ方：指定始点下の実 comma の相対反映。 -/
lemma fullyFaithful_pullback_snd_endpointTransport {C K X : SSet.{u}}
    [Quasicategory C] [Quasicategory X] (δ : C ⟶ X) (hδ : IsFullyFaithful δ)
    {r s : K ⟶ X} (h : r = s) :
    IsFullyFaithful (pullback.snd δ (sliceOverProjection r) ≫
      eqToHom (congrArg sliceOver h)) := by
  subst s
  simpa only [eqToHom_refl, Category.comp_id] using
    fullyFaithful_pullback_snd_of_innerFibration_right hδ (sliceOverProjection r)
variable (κ : Cardinal.{u}) {K C : SSet.{u}} [Quasicategory C]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ IndInfinity κ C) (k : K _⦋0⦌)
local notation "p" => SSet.yonedaEquiv.symm (functorVertex D)
local notation "e" => evaluateFunctorAt (Y := IndInfinity κ C) (ULift.up k)
local notation "v" => D.app (Opposite.op ⦋0⦌) (ULift.up k)
/-- 概要：元の全関手の指定点評価は、元の D の同じ指定点の値。
方針：Yoneda の頂点と評価の可換性を使う。
規約：元の全射と指定値を保持する。
使われ方：指定始点下の実 comma の相対反映。 -/
lemma diagramCommaEvaluation_point : p ≫ e = SSet.yonedaEquiv.symm v := by
  rw [SSet.yonedaEquiv_symm_comp, diagramCommaEvaluation_vertex]
/-- 概要：scalar comma の第二射影を、全図式の評価で得た指定終点に揃える。
方針：指定点の等号で終点表示を移す。
規約：元の全射と指定値を保持する。
使われ方：指定始点下の実 comma の相対反映。 -/
def diagramCommaEvaluationSliceProjection :=
  commaSliceEndpointProjection (indYoneda κ C) (diagramCommaEvaluation_point κ D k).symm
/-- 概要：指定終点に揃えた第二射影からも、元の全余錐を厳密に回収する。
方針：全余錐の輸送公式を適用する。
規約：元の全射と指定値を保持する。
使われ方：指定始点下の実 comma の相対反映。 -/
lemma diagramCommaEvaluationSliceProjection_uncurry {T : SSet.{u + 1}}
    (a : T ⟶ leftKanShape (indYoneda κ C) v) :
    sliceOverUncurry (a ≫ diagramCommaEvaluationSliceProjection κ D k) =
    sliceOverUncurry (a ≫ pullback.snd (indYoneda κ C)
      (sliceOverProjection (SSet.yonedaEquiv.symm v))) := by
  have h := sliceOverUncurry_endpointTransport (diagramCommaEvaluation_point κ D k).symm
    (a ≫ pullback.snd (indYoneda κ C) (sliceOverProjection (SSet.yonedaEquiv.symm v)))
  convert h using 1
  rfl

/-- 概要：元の Yoneda が充満忠実なので、終点を揃えた第二射影も充満忠実。
方針：元の第二射影の充満忠実性を移す。
規約：元の全射と指定値を保持する。
使われ方：指定始点下の実 comma の相対反映。 -/
lemma diagramCommaEvaluationSliceProjection_isFullyFaithful :
    IsFullyFaithful (diagramCommaEvaluationSliceProjection κ D k) :=
  fullyFaithful_pullback_snd_endpointTransport (indYoneda κ C)
    (indYoneda_isFullyFaithful κ C) (diagramCommaEvaluation_point κ D k).symm
/-- 概要：元の全評価と scalar slice 射影は、同じ全 slice 後合成の正方形を与える。
方針：両経路の全余錐を uncurry して比較する。
規約：元の全射と指定値を保持する。
使われ方：指定始点下の実 comma の相対反映。 -/
lemma diagramCommaEvaluation_slice_square :
    diagramCommaEvaluation κ D k ≫ diagramCommaEvaluationSliceProjection κ D k =
      diagramCommaSliceProjection κ D ≫ sliceOverPostcomp p e := by
  apply sliceOverUncurry_injective
  rw [diagramCommaEvaluationSliceProjection_uncurry, sliceOverUncurry_postcomp]
  have h := diagramCommaEvaluation_uncurry κ D k (𝟙 (diagramComma κ D))
  simpa only [Category.id_comp] using h
end SerrePositivity.InfinityCategories.F2.Ind
