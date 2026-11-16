module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanHammockHomInfinity
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanHammockHomPinchedValue

/-!
概要：全 Yoneda 比較に使う同じ恒等係数を元の hammock 零単体へ回収する。
方針：原本の全 coslice 比較の恒等点公式と同じ源関手の恒等射保存を合成する。
規約：原本の全比較と異なる恒等点を選ばない。
使われ方：全図式 Yoneda 比較と元の局所化辺の零単体照合を結ぶ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open _root_.CategoryTheory _root_.SSet _root_.Opposite _root_.SerrePositivity.EInfinity.Hammock
open _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X : C.category)

/-- 概要：正本 Yoneda の同じ恒等点は元の通常恒等射の hammock 零単体。
方針：同じ源関手の恒等射保存と実 Hom 点の公式を評価する。
規約：対象宇宙の持ち上げは Hom を変更しない。
使われ方：原本の全 Yoneda 比較の始点の正規化。 -/
lemma kanHammockYonedaIdentity_zero :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.representableHomIdentity
      (D := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CoherentObjectLift (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanHammockCategory C))
      (ULift.up ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).obj X)) =
    SSet.unitHomEquiv _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap C.weakEquivalences (𝟙 X) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph C.weakEquivalences X X)) := by
  change SSet.unitHomEquiv _ (eId SSet ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).obj X)) = _
  apply congrArg (SSet.unitHomEquiv _)
  have h := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor_homTo C (𝟙 X)
  rw [(_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).map_id X, ForgetEnrichment.homTo_id] at h
  exact h

/-- 概要：同じ全 coslice 比較の恒等錐は元の恒等射の零単体を回収する。
方針：原本の恒等錐評価と同じ恒等点の正規化を合成する。
規約：全 Yoneda 同型の定義と同じ全空間射を使う。
使われ方：全図式の比較と元の局所化射の零単体回収の接続。 -/
lemma kanHammockYonedaCosliceIdentity_zero :
    let x : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CoherentObjectLift (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanHammockCategory C) :=
      ULift.up ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).obj X)
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberVertexEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representableHomFunctor x).obj x)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.KanCosliceComparison.fiberIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representableHomFunctor x) x).hom.app (op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.KanCosliceComparison.start (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representableHomFunctor x) x
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.representableHomIdentityCoefficient x))) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.representableHomIdentity x :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.representableHomCosliceIdentity_value
    (D := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CoherentObjectLift (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanHammockCategory C))
    (ULift.up ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).obj X))

/-- 概要：同じ大域 Yoneda 射の全 Hom 上の fiber は同じ恒等係数への合成作用。
方針：原本の全 fiber 作用同型へ同じ元の Kan hammock と恒等点を代入する。
規約：別の点ごとの比較射を選ばない。
使われ方：元の射の零単体を同じ全 Yoneda 比較の中で追跡する。 -/
def kanHammockYonedaFiberActionIso (Y : C.category) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.KanCosliceComparison.fiber_actionIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representableHomFunctor (D := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CoherentObjectLift (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanHammockCategory C))
      (ULift.up ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).obj X)))
    (ULift.up ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).obj X))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.representableHomIdentityCoefficient
      (D := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CoherentObjectLift (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanHammockCategory C))
      (ULift.up ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).obj X)))
    (ULift.up ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).obj Y))

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
