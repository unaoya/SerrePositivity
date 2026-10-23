module

public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedTransportUnit
public import SerrePositivity.InfinityCategories.F1.Transport.PointFunctorEvaluation

/-!
概要：weighted nerve の strict transport への自然な単位比較は Kan 値で成分ごとに同値。
方針：under 圏の恒等射での評価との合成を既存の weighted nerve の fiber 同型と同定する。
規約：比較射は自然に構成した射のまま保持し、成分の逆は同値判定から取る。
使われ方：Kerodon 5.3.5.7、7.5.4.6 の元の strict な係数図式の回収。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {I : Type u} [SmallCategory I]

/-- 概要：under 圏の恒等射で輸送の族を評価すると元の値の weighted nerve への定値包含になる。
方針：全ての構造射が恒等射となり、H の恒等射の保存で係数を簡約する。
規約：元の係数図式に Kan 性は要求しない。
使われ方：Kerodon 5.3.5.7、7.5.4.6 の単位比較の fiber での計算。 -/
lemma weightedTransportFamily_identity (H : I ⥤ SSet.{u}) (i : I) :
    lift (SSet.const (strictTransportUnderIdentityVertex i)) (𝟙 (H.obj i)) ≫
      weightedTransportFamily H i = weightedNerveConstantLift H i := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  change (⟨(Functor.const (Fin (n + 1))).obj i, weightedTransportCoefficients H
      ((Functor.const (Fin (n + 1))).obj (Under.mk (𝟙 i))) (SSet.yonedaEquiv.symm a)⟩ :
        weightedNerveSimplex H n) =
    ⟨(Functor.const (Fin (n + 1))).obj i, weightedNerveConstantDiagram H i a⟩
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  apply NatTrans.ext
  funext k
  change stdSimplex.map (simplexPrefixInclusion k.val n _) ≫
    SSet.yonedaEquiv.symm a ≫ H.map (𝟙 i) =
      stdSimplex.map (simplexPrefixInclusion k.val n _) ≫ SSet.yonedaEquiv.symm a
  rw [H.map_id, Category.comp_id]

/-- 概要：単位比較の恒等射評価を全空間へ含めると元の値の定値包含になる。
方針：curry の頂点評価を輸送の族に適用し、恒等射の計算を使う。
規約：strict transport の既存の評価射をそのまま使う。
使われ方：Kerodon 5.3.5.7、7.5.4.6 の自然な比較と fiber 比較の可換性。 -/
lemma weightedTransportUnitComponent_evaluate_ι (H : I ⥤ SSet.{u}) (i : I) :
    weightedTransportUnitComponent H i ≫ leftStrictTransportEvaluate (weightedNerveProjection H) i ≫
        vertexFiberι (weightedNerveProjection H) (nerveVertex i) =
      weightedNerveConstantLift H i := by
  change curry (weightedTransportFamily H i) ≫
    evaluateFunctorAt (strictTransportUnderIdentityVertex i) = _
  rw [curry_evaluateFunctorAt_vertex, weightedTransportFamily_identity]

/-- 概要：単位比較と strict transport の恒等射評価の合成は weighted nerve の標準 fiber 同型。
方針：fiber の包含後の等式で射を比較する。
規約：等式は実際の比較射の合成である。
使われ方：Kerodon 5.3.5.7、7.5.4.6 の成分ごとの同値性の二対三判定。 -/
lemma weightedTransportUnitComponent_evaluate (H : I ⥤ SSet.{u}) (i : I) :
    weightedTransportUnitComponent H i ≫ leftStrictTransportEvaluate (weightedNerveProjection H) i =
      weightedNerveFiberMap H i := by
  apply vertexFiber_hom_ext (weightedNerveProjection H) (nerveVertex i)
  rw [Category.assoc, weightedTransportUnitComponent_evaluate_ι]
  rfl

/-- 概要：Kan 値図式から weighted nerve の strict transport への自然な比較は成分ごとに圏同値。
方針：恒等射での評価の同値性と、合成が fiber 同型であることを二対三で使う。
規約：全ての係数値の Kan 性だけを要求する。
使われ方：Kerodon 5.3.5.7、7.5.4.6 の元の図式と strict transport の比較。 -/
lemma weightedTransportUnitComponent_isQCatEquivalence (H : I ⥤ SSet.{u})
    [∀ i, KanComplex (H.obj i)] (i : I) :
    IsQCatEquivalence (weightedTransportUnitComponent H i) := by
  have := leftStrictTransport_kanComplex (weightedNerveProjection H) i
  have := weightedNerveFiber_kanComplex H i
  apply (leftStrictTransportEvaluate_isQCatEquivalence (weightedNerveProjection H) i).cancel_right
  rw [weightedTransportUnitComponent_evaluate]
  exact (qCatEquivalenceOfIso (asIso (weightedNerveFiberMap H i))).isQCatEquivalence

/-- 概要：Kan 値図式から weighted nerve の strict transport への自然な比較は成分ごとにホモトピー同値。
方針：両側の Kan 性と圏同値判定から実際の単体的ホモトピー逆を得る。
規約：成分の逆の族が自然変換になるとは主張しない。
使われ方：Kerodon 5.3.5.7、7.5.4.6 の end の同値不変性へ渡す自然な比較。 -/
lemma weightedTransportUnitComponent_homotopyEquivalence (H : I ⥤ SSet.{u})
    [∀ i, KanComplex (H.obj i)] (i : I) :
    IsSimplicialHomotopyEquivalence (weightedTransportUnitComponent H i) := by
  have := leftStrictTransport_kanComplex (weightedNerveProjection H) i
  exact (weightedTransportUnitComponent_isQCatEquivalence H i).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.HomotopyLimits
