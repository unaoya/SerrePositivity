module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.KST.Fibration.CocartesianKanDiagram
public import SerrePositivity.InfinityCategories.Derived.KanModels.GroupoidCompletionKanComparison
public import SerrePositivity.KST.Fibration.WeakSpanDenominatorBaseChange
public import SerrePositivity.KST.LocalizingInvariants.MarkedSpanFamilyFiber
public import SerrePositivity.InfinityCategories.F1.Transport.SimplexFirstVertex
public import SerrePositivity.InfinityCategories.Core.VertexFiberNervePullback

/-! # 元の全 W 分数 span の単体圏上の厳密 Kan 図式と両端固定の値の比較 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.Fibration
variable {A B : StableCategory.{u}} (i : ExactMap A B) (x : B.obj _⦋0⦌)

/-- 元の固定第一終点 span 族を、底の全単体圏の初頂点写像に沿って厳密に引き戻す。 -/
def weakSpanSimplexProjection :
    pullback (markedSpanFamilyProjection B.obj (weakEquivalences i) x)
        (transportSimplexFirstVertexMap B.obj) ⟶ nerve (TransportSimplexCategory B.obj) :=
  pullback.snd _ _

instance weakSpanSimplexProjection_cocartesianFibration :
    CocartesianFibration (weakSpanSimplexProjection i x) :=
  weakSpanBaseChange_cocartesianFibration (i := i) x (transportSimplexFirstVertexMap B.obj)

/-- 全 cocartesian section の厳密輸送に関手的な Kan 模型を適用した図式。 -/
def weakSpanKanDiagram : TransportSimplexCategory B.obj ⥤ KanObject.{u} :=
  cocartesianKanDiagram (weakSpanSimplexProjection i x)

/-- 同じ図式の全単体上の coherent な空間値表示。底への降下はまだ主張しない。 -/
def weakSpanKanCoherentDiagram :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve (TransportSimplexCategory B.obj)) ⟶
      SpaceInfinity.{u} :=
  kanDiagramCoherentNerve (weakSpanKanDiagram i x)

/-- 指定した全単体圏の対象に対する実 fiber は、元の両端固定分数 span と厳密同型。 -/
def weakSpanSimplexFiberIso (c : TransportSimplexCategory B.obj) :
    fixedMarkedSpans B.obj (weakEquivalences i) x
        ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌) (nerveVertex c)) ≅
      vertexFiber (weakSpanSimplexProjection i x) (nerveVertex c) :=
  markedSpanFamilyFiberIso _ _ _ _ ≪≫
    (SerrePositivity.InfinityCategories.vertexFiberPullbackIso _ _ _).symm

/-- 同じ恒等射評価と fiber 同型で、各図式値を元の固定分数の厳密 Kan 模型へ送る。 -/
def weakSpanKanValueComparison (c : TransportSimplexCategory B.obj) :
    ((weakSpanKanDiagram i x).obj c).obj ⟶
      (strictKanCompletion.obj (fixedMarkedSpans B.obj (weakEquivalences i) x
        ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌) (nerveVertex c)))).obj :=
  cocartesianKanDiagramFiberComparison (weakSpanSimplexProjection i x) c ≫
    strictKanCompletion.map (weakSpanSimplexFiberIso i x c).inv

/-- 元の各値の比較射は、実際の Kan 同値。 -/
theorem weakSpanKanValueComparison_isQCatEquivalence (c : TransportSimplexCategory B.obj) :
    IsQCatEquivalence (weakSpanKanValueComparison i x c) :=
  (cocartesianKanDiagramFiberComparison_isQCatEquivalence (weakSpanSimplexProjection i x) c).comp
    (strictKanCompletion_map_isQCatEquivalence (weakSpanSimplexFiberIso i x c).inv
      (by infer_instance))

/-- 同じ図式値と、元の全辺局所化による固定分数 span の亜群化の実同値。 -/
def weakSpanKanValueGroupoidEquivalence (c : TransportSimplexCategory B.obj) :
    QCatEquivalence (((weakSpanKanDiagram i x).obj c).obj)
      (groupoidCompletion (fixedMarkedSpans B.obj (weakEquivalences i) x
        ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌) (nerveVertex c)))) :=
  (weakSpanKanValueComparison_isQCatEquivalence i x c).choose.trans
    (groupoidCompletionKanComparison_isQCatEquivalence _).choose.symm

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanCoherentDiagram (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanCoherentDiagram := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanCoherentDiagram

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanDiagram (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanDiagram := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanDiagram

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanValueComparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanValueComparison := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanValueComparison

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanValueComparison_isQCatEquivalence := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanValueComparison_isQCatEquivalence

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanValueGroupoidEquivalence (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanValueGroupoidEquivalence := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanValueGroupoidEquivalence

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanSimplexFiberIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanSimplexFiberIso := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanSimplexFiberIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanSimplexProjection (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanSimplexProjection := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanSimplexProjection

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanSimplexProjection_cocartesianFibration (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanSimplexProjection_cocartesianFibration := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanSimplexProjection_cocartesianFibration

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanValueGroupoidEquivalence._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanValueGroupoidEquivalence._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanValueGroupoidEquivalence._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanValueGroupoidEquivalence._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanValueGroupoidEquivalence._proof_3 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanValueGroupoidEquivalence._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanValueGroupoidEquivalence._proof_4 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanValueGroupoidEquivalence._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanSimplexProjection._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanSimplexProjection._proof_1
