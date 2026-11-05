module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Core.FunctorIsoTransport
public import SerrePositivity.KST.Fibration.WeakSpanKanSpaceInversion
public import SerrePositivity.KST.Fibration.SpaceDiagramLocalizationDescent

/-! # 元の Verdier 商への同じ coherent 分数図式の全関手 ∞ 圏による降下 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.Fibration
variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  (h : IsVerdierSequence i q) (x : B.obj _⦋0⦌)

/-- 宇宙を合わせた元の Verdier 商上の、固定第一終点の coherent 分数図式。 -/
def weakSpanKanQuotientDiagram :
    (SSet.uliftFunctor.{u + 1, u}).obj C.obj ⟶ SpaceInfinity.{u} :=
  spaceDiagramLocalizationDescend q.hom (weakEquivalences i) h.quotient
    (weakSpanKanSpaceDiagram i x) (weakSpanKanSpaceDiagram_inverts_weak h x)

/-- 商関手による制限は、元の底上の同じ図式と全関手圏内で自然同型。 -/
def weakSpanKanQuotientDiagram_restrictionIso :
    FunctorIso ((SSet.uliftFunctor.{u + 1, u}).map q.hom ≫ weakSpanKanQuotientDiagram h x)
      (weakSpanKanSpaceDiagram i x) :=
  spaceDiagramLocalizationDescendIso q.hom (weakEquivalences i) h.quotient
    (weakSpanKanSpaceDiagram i x) (weakSpanKanSpaceDiagram_inverts_weak h x)

/-- 元の全単体圏までの制限も、元の strict section の coherent 図式を自然同型で回収する。 -/
def weakSpanKanQuotientDiagram_simplexIso :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B.obj ≫ q.hom) ≫
        weakSpanKanQuotientDiagram h x) (weakSpanKanCoherentDiagram i x) := by
  have e := (weakSpanKanQuotientDiagram_restrictionIso h x).precomp
    ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B.obj))
  exact F2.functorIsoOfEq e (by rw [← Category.assoc, ← Functor.map_comp]) rfl ≪≫
    weakSpanKanSpaceDiagram_restrictionIso i x

/-- 商上の図式の元の初頂点での値は、同じ strict Kan 分数模型の値と実際に同型。 -/
def weakSpanKanQuotientDiagram_initialVertexIso (c : TransportSimplexCategory B.obj) :
    VertexIso ((weakSpanKanQuotientDiagram h x).app (Opposite.op ⦋0⦌)
      (ULift.up (q.hom.app (Opposite.op ⦋0⦌)
        ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌) (nerveVertex c)))))
      (spaceInfinityVertex ((weakSpanKanDiagram i x).obj c)) :=
  (weakSpanKanQuotientDiagram_restrictionIso h x).app
    (ULift.up ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌) (nerveVertex c))) ≪≫
      weakSpanKanSpaceDiagram_initialVertexIso i x c

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientDiagram := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram_initialVertexIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientDiagram_initialVertexIso := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram_initialVertexIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram_restrictionIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientDiagram_restrictionIso := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram_restrictionIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram_simplexIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientDiagram_simplexIso := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram_simplexIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientDiagram_initialVertexIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram_initialVertexIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientDiagram_simplexIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram_simplexIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientDiagram_simplexIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram_simplexIso._proof_2
