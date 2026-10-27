module

public import SerrePositivity.KST.Spectra.D3PointedKanCofiberCone
public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictConeSimplex

/-!
概要：通常の引き戻し錐を実四角形へ移し、その二三角形を同じ二つの合成射列で回収する。
方針：同じ strict 錐を cospan ホーンへ制限し、全単体の錐制限公式を適用する。
規約：錐の頂点や脚を選び直さず、二つの三角形そのものを比較する。
使われ方：構成済み実端点パラメータ四角形への極限性の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
namespace SerrePositivity.KST.Spectra.D3StrictPullbackSquare
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
  {E X B : C} {f : E ⟶ B} {g : X ⟶ B} (c : PullbackCone f g)

/-- 同じ通常の引き戻し錐の、元の二辺を指定したホーン上の coherent 錐。 -/
def cone : JoinCone
    (edgeCospan (coherentNerveEdge f).toTruncated (coherentNerveEdge g).toTruncated) :=
  (DiagramLimitTransport.restrict
    (strictCoherentCone (c.whisker (AsSmall.down : AsSmall.{u} WalkingCospan ⥤ WalkingCospan)))
    CospanShape.strictCospanHornIso.inv).cast (CospanShape.strictDiagram_eq f g)

/-- 同じ錐を四角形へ移した実図式。 -/
def square : ((Δ[1] : SSet.{max u v}) ⊗ Δ[1]) ⟶ SimplicialNerve C := coneSquare (cone c)

/-- 下側の実三角形は、同じ fst と元の右辺の strict 合成表示。 -/
lemma triangle_left : squareTriangle 1 ≫ square c =
    SSet.yonedaEquiv.symm ((nerveToCoherent C).app (Opposite.op ⦋2⦌)
      (ComposableArrows.mk₂ c.fst f)) := by
  rw [← cospanConeSquareIso_left]
  change (cospanConeTriangleLeft ≫ cospanConeSquareIso.hom) ≫
    (cospanConeSquareIso.inv ≫ (cone c).val) = _
  rw [Category.assoc, Iso.hom_inv_id_assoc]
  change ((joinStdSimplexIso 0 1).inv ≫ joinMap (𝟙 Δ[0]) horn₂₂.ι₀₂) ≫
    (joinMap (𝟙 Δ[0]) CospanShape.strictCospanHornIso.inv ≫
      strictCoherentConeMap (c.whisker AsSmall.down)) = _
  rw [Category.assoc, ← Category.assoc (joinMap _ _), ← joinMap_comp, Category.id_comp,
    strictCoherentConeMap_simplex]
  change (joinStdSimplexIso 0 1).inv ≫ ((joinStdSimplexIso 0 1).hom ≫ _) = _
  rw [Iso.inv_hom_id_assoc]
  apply congrArg SSet.yonedaEquiv.symm
  apply congrArg ((nerveToCoherent C).app _)
  have ha : (SSet.yonedaEquiv (horn₂₂.ι₀₂ ≫
      CospanShape.strictCospanHornIso.{u, v}.inv)).down =
        ComposableArrows.mk₁ (AsSmall.up.map WalkingCospan.Hom.inl) := by
    refine ComposableArrows.ext₁ rfl rfl ?_
    apply ULift.ext
    exact Subsingleton.elim _ _
  rw [ha]
  refine ComposableArrows.ext₂ rfl rfl rfl ?_ ?_
  · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl

/-- 上側の実三角形は、同じ snd と元の上辺の strict 合成表示。 -/
lemma triangle_right : squareTriangle 0 ≫ square c =
    SSet.yonedaEquiv.symm ((nerveToCoherent C).app (Opposite.op ⦋2⦌)
      (ComposableArrows.mk₂ c.snd g)) := by
  rw [← cospanConeSquareIso_right]
  change (cospanConeTriangleRight ≫ cospanConeSquareIso.hom) ≫
    (cospanConeSquareIso.inv ≫ (cone c).val) = _
  rw [Category.assoc, Iso.hom_inv_id_assoc]
  change ((joinStdSimplexIso 0 1).inv ≫ joinMap (𝟙 Δ[0]) horn₂₂.ι₁₂) ≫
    (joinMap (𝟙 Δ[0]) CospanShape.strictCospanHornIso.inv ≫
      strictCoherentConeMap (c.whisker AsSmall.down)) = _
  rw [Category.assoc, ← Category.assoc (joinMap _ _), ← joinMap_comp, Category.id_comp,
    strictCoherentConeMap_simplex]
  change (joinStdSimplexIso 0 1).inv ≫ ((joinStdSimplexIso 0 1).hom ≫ _) = _
  rw [Iso.inv_hom_id_assoc]
  apply congrArg SSet.yonedaEquiv.symm
  apply congrArg ((nerveToCoherent C).app _)
  have ha : (SSet.yonedaEquiv (horn₂₂.ι₁₂ ≫
      CospanShape.strictCospanHornIso.{u, v}.inv)).down =
        ComposableArrows.mk₁ (AsSmall.up.map WalkingCospan.Hom.inr) := by
    refine ComposableArrows.ext₁ rfl rfl ?_
    apply ULift.ext
    exact Subsingleton.elim _ _
  rw [ha]
  refine ComposableArrows.ext₂ rfl rfl rfl ?_ ?_
  · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl


/-- 同じ strict 錐の極限性は、同じホーンへの制限を通して実四角形へ移る。 -/
lemma isPullback [Quasicategory (SimplicialNerve C)]
    (hc : IsLimitCone (strictCoherentCone
      (c.whisker (AsSmall.down : AsSmall.{u} WalkingCospan ⥤ WalkingCospan)))) :
    IsPullbackSquare (square c) := by
  let d := strictCoherentCone
    (c.whisker (AsSmall.down : AsSmall.{u} WalkingCospan ⥤ WalkingCospan))
  let a := CospanShape.strictCospanHornIso.{u, v}.inv
  have := DiagramLimitTransport.restriction_trivial
    (strictCoherentDiagram (AsSmall.down ⋙ cospan f g)) a
    (isPrecompositionEquivalence_of_iso CospanShape.strictCospanHornIso.symm)
  let e := qCatEquivalenceOfTrivialKanFibration
    (sliceOverRestrict (strictCoherentDiagram (AsSmall.down ⋙ cospan f g)) a)
  have hd : IsLimitCone (DiagramLimitTransport.restrict d a) :=
    (e.isTerminalVertex_iff d).1 hc
  exact coneSquare_isPullback (cone c) (hd.cast (CospanShape.strictDiagram_eq f g))

end SerrePositivity.KST.Spectra.D3StrictPullbackSquare
