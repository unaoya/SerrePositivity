module
public import SerrePositivity.KST.Fibration.WeakSpanKanInitialInversion
public import SerrePositivity.InfinityCategories.F1.Transport.LocalizationUlift
public import SerrePositivity.KST.LocalizingInvariants.LocalizationUniqueness

/-! # 全 span の coherent Kan 図式の、元の底への全関手 ∞ 圏による降下 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {A B : StableCategory.{u}} (i : ExactMap A B) (x : B.obj _⦋0⦌)

/-- 元の単体圏上の全分数図式を、宇宙を揃えた元の底上の空間値図式へ降下する。 -/
def weakSpanKanSpaceDiagram : (SSet.uliftFunctor.{u + 1, u}).obj B.obj ⟶ SpaceInfinity.{u} :=
  localizationDescend
    ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B.obj))
    (transportSimplexInitialEdgesLifted B.obj)
    (transportSimplexFirstVertexMap_ulift_isLocalization B.obj)
    (weakSpanKanCoherentDiagram i x) (weakSpanKanCoherentDiagram_inverts_initial i x)

/-- 初頂点写像による制限は、元の全 coherent 分数図式と全関手圏内で自然同型。
各値だけの選択から降下を推論せず、同じ局所化普遍性の実因子化同型を保持する。 -/
def weakSpanKanSpaceDiagram_restrictionIso :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B.obj) ≫
        weakSpanKanSpaceDiagram i x) (weakSpanKanCoherentDiagram i x) :=
  localizationDescendIso
    ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B.obj))
    (transportSimplexInitialEdgesLifted B.obj)
    (transportSimplexFirstVertexMap_ulift_isLocalization B.obj)
    (weakSpanKanCoherentDiagram i x) (weakSpanKanCoherentDiagram_inverts_initial i x)

/-- 降下した図式の初頂点での値は、元の同じ厳密 Kan 分数模型の空間を表す。 -/
def weakSpanKanSpaceDiagram_initialVertexIso (c : TransportSimplexCategory B.obj) :
    VertexIso ((weakSpanKanSpaceDiagram i x).app (Opposite.op ⦋0⦌)
      (ULift.up ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌) (nerveVertex c))))
      (spaceInfinityVertex ((weakSpanKanDiagram i x).obj c)) := by
  have e := (weakSpanKanSpaceDiagram_restrictionIso i x).app (ULift.up (nerveVertex c))
  have hv : (weakSpanKanCoherentDiagram i x).app (Opposite.op ⦋0⦌)
      (ULift.up (nerveVertex c)) = spaceInfinityVertex ((weakSpanKanDiagram i x).obj c) :=
    kanDiagramCoherentNerve_vertex (weakSpanKanDiagram i x) c
  exact e ≪≫ eqToIso (congrArg SSet.HomotopyCategory.mk hv)

end SerrePositivity.KST.Fibration
