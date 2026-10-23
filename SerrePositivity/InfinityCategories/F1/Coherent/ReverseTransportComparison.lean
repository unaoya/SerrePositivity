module

public import SerrePositivity.InfinityCategories.F1.Coherent.CompositionReverse
public import SerrePositivity.InfinityCategories.F1.Transport.FiberTransportFamilySourceComparison
public import SerrePositivity.InfinityCategories.F1.Coherent.HomEquivalence
public import SerrePositivity.InfinityCategories.HomotopyLimits.OppositeKanHomotopy

/-!
概要：反転した coherent 合成の輸送を左 coslice の普遍輸送へ結び付ける。
方針：底の区間比較の端点を計算し、任意の係数射の比較を標準輸送へ適用する。
規約：局所 Kan 性だけを用い、モデル構造の instance は要求しない。
使われ方：普遍 pointed-space 輸送の写像空間上の同値性への還元。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：反転した Hom の区間族の始点は元の終域 Y。
方針：区間の反転の端点公式と右 Hom の区間比較の終点公式を使う。
規約：底は coherent nerve の反対。
使われ方：普遍輸送へのパラメーター射の始点条件。 -/
lemma coherentReverseHomInterval_zero {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (X Y : C) :
    prismEndpoint 0 _ ≫ coherentReverseHomInterval X Y =
      SSet.const (SSet.opObjEquiv.symm (coherentNerveVertex Y)) := by
  dsimp only [coherentReverseHomInterval]
  rw [reversePrism_endpoint, show (0 : Fin 2).rev = 1 by decide,
    intervalMappingUncurry_one]
  rfl

/-- 概要：反転した Hom の区間族の終点は元の始域 X。
方針：区間の反転の端点公式と右 Hom の区間比較の始点公式を使う。
規約：底は coherent nerve の反対。
使われ方：普遍輸送へのパラメーター射の終点条件。 -/
lemma coherentReverseHomInterval_one {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (X Y : C) :
    prismEndpoint 1 _ ≫ coherentReverseHomInterval X Y =
      SSet.const (SSet.opObjEquiv.symm (coherentNerveVertex X)) := by
  dsimp only [coherentReverseHomInterval]
  rw [reversePrism_endpoint, show (1 : Fin 2).rev = 0 by decide,
    intervalMappingUncurry_zero]
  rfl

/-- 概要：反転した coherent 合成の作用は左 coslice の普遍輸送と関手同型。
方針：全パラメーターの標準合成輸送に任意の始点係数射の普遍比較を適用する。
規約：頂点ごとの同型ではなく写像空間への射の一つの同型。
使われ方：豊穣な一点 Hom の合成から普遍輸送の同値性を得る。 -/
def coherentCompositionReverseTransport_parametrizedIso {C : Type v} [Category.{u} C]
    [SimplicialCategory C] [∀ A B : C, KanComplex (SimplicialCategory.sHom A B)]
    (X Y Z : C) :
    FunctorIso (coherentCompositionReverseTransportFamily X Y Z).map
      (intervalMappingCurryOfEndpoints (coherentReverseHomInterval X Y)
        (coherentReverseHomInterval_zero X Y) (coherentReverseHomInterval_one X Y) ≫
      parametrizedFiberTransport
        (sliceUnderProjection (SSet.yonedaEquiv.symm
          (SSet.opObjEquiv.symm (coherentNerveVertex Z))))
        (SSet.opObjEquiv.symm (coherentNerveVertex Y))
        (SSet.opObjEquiv.symm (coherentNerveVertex X)) ≫
      (pre (coherentReverseSliceFiberComparison Y Z)).app
        (vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm
          (SSet.opObjEquiv.symm (coherentNerveVertex Z))))
          (SSet.opObjEquiv.symm (coherentNerveVertex X)))) :=
  (coherentCompositionReverseTransportFamily X Y Z).mapIso_parametrizedSource _ _ _
    (coherentReverseHomInterval_zero X Y) (coherentReverseHomInterval_one X Y)

/-- 概要：反転した Hom の左 coslice fiber 比較は局所 Kan 性の下でホモトピー同値。
方針：右 Hom 比較と fiber 同型の合成を反転し、反転 fiber 同型を合成する。
規約：反対 nerve の左 coslice を値域とする実際の射についての主張。
使われ方：普遍輸送の比較で始点と終点の係数変更を消去する。 -/
lemma coherentReverseSliceFiberComparison_homotopyEquivalence {C : Type v} [Category.{u} C]
    [SimplicialCategory C] [∀ A B : C, KanComplex (SimplicialCategory.sHom A B)]
    (X Z : C) : IsSimplicialHomotopyEquivalence (coherentReverseSliceFiberComparison X Z) := by
  have h₀ := (coherentHomComparison_isQCatEquivalence X Z).comp
    (qCatEquivalenceOfIso (pinchedHomSliceFiberIso (coherentNerveVertex X)
      (coherentNerveVertex Z))).isQCatEquivalence
  have h₁ := HomotopyLimits.oppositeKanHomotopyEquivalence h₀.isSimplicialHomotopyEquivalence
  let e := qCatEquivalenceOfIso
    (pointSliceReverseFiberIso (coherentNerveVertex Z) (coherentNerveVertex X))
  exact h₁.comp e.isQCatEquivalence.isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories
