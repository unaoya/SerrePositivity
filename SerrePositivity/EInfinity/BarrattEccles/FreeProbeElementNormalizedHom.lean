module
public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeElementColumn
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.WeakAnodyneLocalization
public import SerrePositivity.EInfinity.BarrattEccles.FreeDerivedHomSpanEquivalence
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorElementParameterEquivalence
/-! 概要：元の全要素の随伴評価を同じ正規化自由 Hom の全要素圏へ送る。
方針：元の標的 augmentation と実自由忘却 Hom 同型を使う。
規約：元の全単体・同じ評価射とパラメータを保持する。
使われ方：元の全 pinched 族と正規化自由 roof の弱比較。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel _root_.SerrePositivity.ComplexLimits
variable (A : Type u) [CommRing A] (X : Complex A) (B : (operad A).Algebra)

/-- 概要：元の標的置換の正規化 Hom から同じ自由 Hom への実写像。
方針：元の augmentation と同じ随伴 Hom 同型の逆を合成する。
規約：元の全 Hom を保持。使われ方：同じ全要素の代数評価。 -/
def freeProbeElementNormalizedHomMap :
    ((_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorHom A).obj (op X)).obj (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A B.carrier).val ⟶
      ((freeNormalizedProbeHom A).obj (op X)).obj B :=
  _root_.SerrePositivity.ComplexLimits.normalizedProbeTargetReplacementMap A X B.carrier ≫
    (((freeNormalizedProbeHomAdjunctionIso A).inv.app (op X)).app B)

/-- 概要：同じ実 Hom 写像はホモトピー同値。
方針：元の標的弱比較と実随伴 Hom 同型を使う。
規約：別の Hom 同値に置換しない。使われ方：全要素圏写像の反転性。 -/
lemma freeProbeElementNormalizedHomMap_homotopyEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (freeProbeElementNormalizedHomMap A X B) := by
  have := _root_.SerrePositivity.ComplexLimits.normalizedProbeTensorHom_kanComplex A (op X)
    (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A B.carrier).val
  have := _root_.SerrePositivity.ComplexLimits.normalizedProbeTensorHom_kanComplex A (op X) B.carrier
  have := freeNormalizedProbeHom_kanComplex A (op X) B
  exact (_root_.SerrePositivity.ComplexLimits.normalizedProbeTargetReplacementMap_homotopyEquivalence A X B.carrier).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialHomotopyEquivalence_iso_hom
      (((freeNormalizedProbeHomAdjunctionIso A).app (op X)).app B).symm)

/-- 概要：同じ Hom 写像の各単体は元の評価と同じ随伴像。
方針：元の実 Hom 同型の逆を評価する。
規約：元の複体射を保持。使われ方：同じ二列 roof の全回収。 -/
lemma freeProbeElementNormalizedHomMap_apply (n : SimplexCategory)
    (f : ((_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorFrame A).obj X).obj n ⟶
      (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A B.carrier).val) :
    (freeProbeElementNormalizedHomMap A X B).app (op n) f =
      ((operad A).freeAlgebraAdjunction.homEquiv _ B).symm
        (f ≫ _root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValueAugmentation A B.carrier) := rfl

/-- 概要：元の全要素圏から同じ正規化自由 Hom の要素圏への実関手。
方針：元の要素の Hom 宇宙を揃え、同じ実 Hom 写像を要素に適用する。
規約：元の全単体を保持。使われ方：元の全屋根の同定。 -/
def freeProbeElementNormalizedIndexMap : freeProbeElementIndex A X B ⥤
    ULiftHom.{u + 1} (((((freeNormalizedProbeHom A).obj (op X)).obj B).Elements)ᵒᵖ) :=
  _root_.SerrePositivity.ComplexLimits.normalizedTensorElementLiftMap A ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X)
    (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A B.carrier).val ⋙
    ULiftHom.down.{0, u, u + 1} ⋙
      (freeProbeElementNormalizedHomMap A X B).mapElements.op ⋙ ULiftHom.up.{0, u, u + 1}

/-- 概要：異なる対象・Hom 宇宙を持つ元の全要素写像の実 nerve。
方針：各全単体列を同じ元の関手で後合成する。
規約：全パラメータを保持。使われ方：同じ全 Hom への弱比較。 -/
def freeProbeElementNormalizedIndexNerveMap : nerve (freeProbeElementIndex A X B) ⟶
    nerve (ULiftHom.{u + 1}
      (((((freeNormalizedProbeHom A).obj (op X)).obj B).Elements)ᵒᵖ)) where
  app _ := ↾fun Γ => Γ ⋙ freeProbeElementNormalizedIndexMap A X B
  naturality _ _ _ := rfl

/-- 概要：全要素圏の同じ写像は元の Hom 係数写像と可換。
方針：元の終端 augmentation の全自然性を使う。
規約：全パラメータを保持。使われ方：全 roof パラメータの弱比較。 -/
lemma freeProbeElementNormalizedIndexMap_parameter :
    freeProbeElementNormalizedIndexNerveMap A X B ≫
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.liftedAugmentation
        (((freeNormalizedProbeHom A).obj (op X)).obj B) =
    _root_.SerrePositivity.ComplexLimits.normalizedTensorElementParameterMap A ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X)
      (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A B.carrier).val ≫
      SSet.uliftFunctor.{u + 1, u}.map (freeProbeElementNormalizedHomMap A X B) := by
  have h := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.liftedAugmentation_naturality.{u, u + 1}
    (freeProbeElementNormalizedHomMap A X B)
  have he : freeProbeElementNormalizedIndexNerveMap A X B =
      _root_.SerrePositivity.ComplexLimits.normalizedTensorElementLiftNerveMap A ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X)
        (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A B.carrier).val ≫
      nerveMap (ULiftHom.down.{0, u, u + 1} ⋙
        (freeProbeElementNormalizedHomMap A X B).mapElements.op ⋙
          ULiftHom.up.{0, u, u + 1}) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro Γ
    exact (CategoryTheory.Functor.assoc Γ
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementLiftMap A ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X)
        (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A B.carrier).val) _).symm
  rw [he, Category.assoc, h, ← Category.assoc]
  rfl

/-- 概要：元の全要素から同じ自由 Hom の要素への写像は反転される。
方針：元の Hom 弱比較と両終端 augmentation の反転性を使う。
規約：実写像自身を検証。使われ方：元の全 pinched 族の弱同値性。 -/
lemma freeProbeElementNormalizedIndexMap_localized_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map (freeProbeElementNormalizedIndexNerveMap A X B)) := by
  have := _root_.SerrePositivity.ComplexLimits.normalizedProbeTensorHom_kanComplex A (op X)
    (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A B.carrier).val
  have := freeNormalizedProbeHom_kanComplex A (op X) B
  have hw := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ulift_homotopyEquivalence
    (freeProbeElementNormalizedHomMap_homotopyEquivalence A X B)
  have := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.anodyneQ_map_isIso_of_weak _ hw.isQCatEquivalence.isWeakHomotopyEquivalence
  have := _root_.SerrePositivity.ComplexLimits.normalizedTensorElementParameterMap_localized_isIso A
    ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X)
    (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A B.carrier).val
  have := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.liftedAugmentation_localized_isIso.{u, u + 1}
    (((freeNormalizedProbeHom A).obj (op X)).obj B)
  have hc : IsIso (AnodyneHomotopy.anodyneQ.map
      (freeProbeElementNormalizedIndexNerveMap A X B) ≫
      AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.liftedAugmentation
        (((freeNormalizedProbeHom A).obj (op X)).obj B))) := by
    rw [← Functor.map_comp, freeProbeElementNormalizedIndexMap_parameter, Functor.map_comp]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp hc

end SerrePositivity.EInfinity.BarrattEccles
