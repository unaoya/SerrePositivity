module

public import SerrePositivity.InfinityCategories.F2.Presentable.HomWeightDiagramComparison
public import SerrePositivity.InfinityCategories.F2.Presentable.LimitDiagramVertexTransport
public import SerrePositivity.InfinityCategories.F1B.NerveComparison.CoconeVertex

/-!
概要：元の前層余極限表示から、同じ全標的 Hom 図式上の極限を構成する。
方針：全 Hom 係数族の極限を、全自然な図式同型で頂点を保持して輸送する。
規約：同じ前層頂点と全係数自然性を保持する。
使われ方：密度表示と Ind bar 表示の共通の Hom 極限の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits
variable {C : SSet.{u}} [Quasicategory C] {D : SSet.{u + 1}} [Quasicategory D]

omit [Quasicategory C] in
/-- 概要：指定前層表示の全係数 Hom 極限を、同じ標的全 Hom 図式へ輸送できる。
方針：同じ反転余錐の全 Hom 極限を図式同型で移し、頂点を計算する。
規約：全前層の元の頂点に対応する自然変換空間を厳密な頂点として持つ。
使われ方：二つの表示の計算を同じ Hom 係数へ帰着する。 -/
lemma exists_homWeight_presentation_limit
    (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D)
    {E : SSet.{u}} (p : (SSet.uliftFunctor.{u + 1, u}).obj E ⟶ PresheafInfinity C)
    (c : JoinCocone p) (hc : IsColimitCone c)
    (H : (SSet.uliftFunctor.{u + 1, u}).obj E ⟶ D)
    (e : FunctorIso ((SSet.uliftFunctor.{u + 3, u + 2}).map (SSet.opFunctor.map
        ((SSet.uliftFunctor.{u + 2, u + 1}).map p)) ≫ fullPresheafHomWeightFamily F₀)
      (canonicalLiftedHomFamily H)) :
    ∃ d : JoinCone (canonicalLiftedHomFamily H), IsLimitCone d ∧
      d.vertex = (fullPresheafHomWeightFamily F₀).app (Opposite.op ⦋0⦌)
        (ULift.up (SSet.opObjEquiv.symm (ULift.up c.vertex))) := by
  let d := mapJoinCone (fullPresheafHomWeightFamily F₀)
    (JoinCone.ulift.{u + 2, u + 3}
      (F1B.coconeReverseCone (JoinCocone.ulift.{u + 1, u + 2} c)))
  have hd := fullPresheafHomWeightFamily_map_isLimit F₀ p c hc
  obtain ⟨d', hd', hv⟩ := exists_limitCone_functorIso_sameVertex e d hd
  refine ⟨d', hd', hv.trans ?_⟩
  dsimp only [d]
  rw [mapJoinCone_vertex, JoinCone.ulift_vertex, F1B.coconeReverseCone_vertex,
    JoinCocone.ulift_vertex]

/-- 概要：表現可能な密度図式の像の全 Hom 図式には元の係数頂点を持つ極限が存在する。
方針：元の全 Yoneda 図式の自然比較を適用する。
規約：元の小図式と指定前層余錐を保持する。
使われ方：局所 Kan 図式の Hom 極限。 -/
lemma exists_homWeight_yonedaPresentation_limit
    (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D)
    {E : SSet.{u}} (p : E ⟶ C)
    (c : JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map p ≫ yonedaInfinityMap C))
    (hc : IsColimitCone c) :
    ∃ d : JoinCone (canonicalLiftedHomFamily ((SSet.uliftFunctor.{u + 1, u}).map p ≫ F₀)),
      IsLimitCone d ∧ d.vertex = (fullPresheafHomWeightFamily F₀).app (Opposite.op ⦋0⦌)
        (ULift.up (SSet.opObjEquiv.symm (ULift.up c.vertex))) :=
  exists_homWeight_presentation_limit F₀ _ c hc _
    (fullPresheafHomWeightFamily_yonedaDiagramIso F₀ p)

end SerrePositivity.InfinityCategories.F2.Presentable
