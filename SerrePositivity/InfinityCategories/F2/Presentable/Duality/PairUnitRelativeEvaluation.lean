module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.PairUnitFiberComparison

/-!
概要：指定随伴単位での右関手族の相対評価と、左関手の全 Hom による単位族を比較する。
方針：同じ単位が左右の固定 coslice の始対象であることを、それぞれの評価の同値性に使う。
規約：元の全自然変換と境界固定パラメータを保持する。実反変関手の Hom 作用との照合は別工程。
使われ方：対ごとの双対性の充満忠実性の入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality
attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：相対評価の終点 fiber を元の同じ二関手上の実単位空間に正規化する。
方針：元の単位の底の等式と固定単位 fiber の厳密な同型を合成する。
規約：単位空間の全高次データを保持する。
使われ方：左右の評価の共通標的。 -/
def pairUnitEvaluationEndpointIso {C D : PresentableInfinityObject.{u}}
    (v₀ v₁ : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌)
    (a : QCatAdjunction (leftVertexFunctor v₀) (rightVertexFunctor w)) :
    vertexFiber (preservingLeftUnitProjection v₁)
      ((preservingLeftUnitProjection v₀).app (Opposite.op ⦋0⦌)
        (preservingLeftUnitVertex v₀ w a)) ≅ PairFixedUnitSpace v₁ w :=
  eqToIso (congrArg (vertexFiber (preservingLeftUnitProjection v₁))
    (preservingLeftUnitVertex_base v₀ w a)) ≪≫ pairLeftUnitFiberIso v₁ w

/-- 概要：全右関手上の相対写像族を指定随伴単位で評価する実際の射。
方針：元の始対象での相対評価を共通の固定単位空間へ続ける。
規約：全相対自然変換と全高次単体を保持する。
使われ方：元の左 Hom 作用との比較。 -/
def pairUnitRelativeEvaluation {C D : PresentableInfinityObject.{u}}
    (v₀ v₁ : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌)
    (a : QCatAdjunction (leftVertexFunctor v₀) (rightVertexFunctor w)) :
    relativeFunctorSpace (preservingLeftUnitProjection v₁) (preservingLeftUnitProjection v₀) ⟶
      PairFixedUnitSpace v₁ w :=
  relativeFunctorEvaluate (preservingLeftUnitProjection v₁) (preservingLeftUnitProjection v₀)
    (preservingLeftUnitVertex v₀ w a) ≫ (pairUnitEvaluationEndpointIso v₀ v₁ w a).hom

/-- 概要：指定随伴単位での全相対関手の評価は自明 Kan fibration。
方針：同じ単位の始対象性で相対評価の全境界持ち上げを得て、標的同型を合成する。
規約：高次の全単体と境界固定を含む結論。
使われ方：単位評価による Hom 比較の同値性。 -/
lemma pairUnitRelativeEvaluation_trivialKanFibration {C D : PresentableInfinityObject.{u}}
    (v₀ v₁ : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌)
    (a : QCatAdjunction (leftVertexFunctor v₀) (rightVertexFunctor w)) :
    TrivialKanFibration (pairUnitRelativeEvaluation v₀ v₁ w a) := by
  have ht := relativeFunctorEvaluate_initial_trivialKanFibration
    (preservingLeftUnitProjection v₁) (preservingLeftUnitProjection v₀)
    (preservingLeftUnitVertex v₀ w a) (preservingLeftUnitVertex_isInitial v₀ w a)
  exact ⟨trivialKanFibrations.comp_mem _ _ ht.mem (MorphismProperty.rlp_of_isIso _ _)⟩

/-- 概要：元の全左 Hom を同じ右関手上の実単位族へ送る。
方針：固定右 coslice の同じ始単位から全左 Hom を持ち上げ、その終点を評価する。
規約：単位は指定した随伴の元の実単位。
使われ方：反変作用の充満忠実性の比較射。 -/
def pairUnitPointHomFamily {C D : PresentableInfinityObject.{u}}
    (v₀ v₁ : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌)
    (a : QCatAdjunction (leftVertexFunctor v₀) (rightVertexFunctor w)) :
    pinchedHomLeft v₀ v₁ ⟶ PairFixedUnitSpace v₁ w :=
  (eqToIso (congrArg (fun z ↦ pinchedHomLeft z v₁)
    (preservingRightUnitVertex_base v₀ w a).symm)).hom ≫
    HomotopyLimits.leftFibrationPointHomFamily (preservingRightUnitProjection w)
      (preservingRightUnitVertex v₀ w a) v₁ ≫ (pairRightUnitFiberIso v₁ w).hom

/-- 概要：元の全左 Hom による指定単位族は QCat 同値。
方針：固定右の同じ単位の始対象性と両端の厳密な同型を使う。
規約：独立な Hom 空間同値であり、元の反変関手の Hom 作用との照合は未主張。
使われ方：相対評価との同じ共通標的による比較。 -/
lemma pairUnitPointHomFamily_isQCatEquivalence {C D : PresentableInfinityObject.{u}}
    (v₀ v₁ : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌)
    (a : QCatAdjunction (leftVertexFunctor v₀) (rightVertexFunctor w)) :
    IsQCatEquivalence (pairUnitPointHomFamily v₀ v₁ w a) := by
  have h := (HomotopyLimits.leftFibrationPointHomFamily_homotopyEquivalence
    (preservingRightUnitProjection w) (preservingRightUnitVertex v₀ w a) v₁
    (preservingRightUnitVertex_isInitial v₀ w a)).isQCatEquivalence
  exact (qCatEquivalenceOfIso (eqToIso (congrArg (fun z ↦ pinchedHomLeft z v₁)
    (preservingRightUnitVertex_base v₀ w a).symm))).isQCatEquivalence.comp
      (h.comp (qCatEquivalenceOfIso (pairRightUnitFiberIso v₁ w)).isQCatEquivalence)

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
