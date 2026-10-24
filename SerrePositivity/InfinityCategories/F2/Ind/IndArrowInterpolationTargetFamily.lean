module

public import SerrePositivity.InfinityCategories.F2.Ind.ArrowInterpolationTargetBoundary
public import SerrePositivity.InfinityCategories.F2.Ind.RightIntervalUniverseTarget
public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowInterpolationTargetEvaluation
public import SerrePositivity.InfinityCategories.F2.Ind.DiagramCommaEvaluation
/-!
概要：元の補間全族の終点評価は、元の終点 comma の全円柱延長の終点面そのもの。
方針：全円柱同型・curry・終点 comma の表示変更を同じ全射で回収する。
規約：元の全図式と全余錐を保持する。
使われ方：指定終点変換を加えた補間余錐と元の試験族の相対比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {κ : Cardinal.{u}} {C A : SSet.{u}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C}
  {q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ diagramComma κ D}
  (V : IndArrowInterpolationData κ D q)
/-- 概要：元の全余錐正方形の終点面は、同じ slice 円柱の終点族の全余錐。
方針：逆比較の終点面を使う。規約：元の射を保持。使われ方：終点評価の相対補間。 -/
lemma indArrowInterpolationSquare_target : SSet.ι₁ ≫ indArrowInterpolationSquare V =
    sliceOverUncurry (SSet.ι₁ ≫ indArrowInterpolationSliceCylinder V) := by
  rw [indArrowInterpolationSquare, ← Category.assoc, arrowInterpolationCoconeIso_inv_target,
    ← sliceOverUncurry_precomp, arrowInterpolationTargetInclusion, Category.assoc,
    indArrowInterpolationGlue_old]
/-- 概要：小さい元の図式の終点評価も、元の全円柱の同じ終点面。
方針：curry と宇宙比較を戻す。規約：元の射を保持。使われ方：終点評価の相対補間。 -/
lemma indArrowInterpolationSmallDiagram_target :
    (SSet.uliftFunctor.{u + 1, u}).map (indArrowInterpolationSmallDiagram V) ≫
      (SSet.uliftFunctor.{u + 1, u}).map
        (evaluateFunctorAt (Y := C) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) =
    SSet.ι₁ ≫ indArrowInterpolationDiagram V := by
  rw [← indArrowFunctorSpace_evaluate (C := C), ← Category.assoc,
    indArrowInterpolationSmallDiagram_lift]
  exact indArrowInterpolationLiftedDiagram_target V
/-- 概要：終点 comma の表示変更は、元の全錐を厳密に保つ。
方針：固定図式の等号を消去する。規約：元の射を保持。使われ方：終点評価の相対補間。 -/
lemma indArrowEndpointCommaIso_uncurry {T : SSet.{u + 1}}
    (a : T ⟶ pullback (indYoneda κ C)
      (sliceOverProjection (stdSimplex.δ 0 ≫ (liftedIntervalToSmall.{u} ≫ D)))) :
    sliceOverUncurry (a ≫ (indArrowEndpointCommaIso κ D).hom ≫
      pullback.snd (indYoneda κ C) (sliceOverProjection (SSet.yonedaEquiv.symm
        (D.app (Opposite.op ⦋0⦌) (ULift.up (stdSimplex.obj₀Equiv.symm (1 : Fin 2))))))) =
    sliceOverUncurry (a ≫ pullback.snd (indYoneda κ C)
      (sliceOverProjection (stdSimplex.δ 0 ≫ (liftedIntervalToSmall.{u} ≫ D)))) := by
  simpa only [indArrowEndpointCommaIso, eqToIso.hom] using
    coneCommaTransport_uncurry (indYoneda κ C) (indArrowEndpoint_point κ D) a
/-- 概要：元の全族の終点評価は、同じ raw 円柱の終点族を表示変更したもの。
方針：実 comma の二成分で検査する。規約：元の射を保持。使われ方：終点評価の相対補間。 -/
lemma indArrowInterpolationCommaFamily_target_raw :
    indArrowInterpolationCommaFamily V ≫
      diagramCommaEvaluation κ D (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
    (SSet.ι₁ ≫ indArrowInterpolationRawCylinder V) ≫ (indArrowEndpointCommaIso κ D).hom := by
  apply pullback.hom_ext
  · simp only [Category.assoc, diagramCommaEvaluation_projection]
    rw [← Category.assoc, indArrowInterpolationCommaFamily_projection,
      indArrowInterpolationSmallDiagram_target]
    have h := congrArg (fun a => SSet.ι₁ ≫ indArrowInterpolationRawCylinder V ≫ a)
      (indArrowEndpointCommaIso_projection κ D)
    convert h.symm using 1
    rfl
  · apply sliceOverUncurry_injective
    simp only [Category.assoc]
    rw [diagramCommaEvaluation_uncurry, indArrowInterpolationCommaFamily_uncurry,
      indArrowInterpolationLiftedCoconeMap_target, indArrowInterpolationSquare_target]
    exact (indArrowEndpointCommaIso_uncurry (a := SSet.ι₁ ≫
      indArrowInterpolationRawCylinder V)).symm
/-- 概要：元の実 comma 全族の終点評価は、指定した同じ拡張の全終点面。
方針：円柱の宇宙比較を消去する。規約：元の射を保持。使われ方：終点評価の相対補間。 -/
lemma indArrowInterpolationCommaFamily_target :
    indArrowInterpolationCommaFamily V ≫
      diagramCommaEvaluation κ D (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
    (SSet.uliftFunctor.{u + 1, u}).map SSet.ι₁ ≫ V.extension := by
  rw [indArrowInterpolationCommaFamily_target_raw, indArrowInterpolationRawCylinder,
    ← Category.assoc SSet.ι₁, rightIntervalUniverseShape_inv_one]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
end SerrePositivity.InfinityCategories.F2.Ind
