module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakComparisonComponentRestriction
public import SerrePositivity.InfinityCategories.F1.Transport.PointedTransformationPointHom

/-! # 同じ商上の成分を、元の全 strict Kan 図式の同じ成分辺へ厳密に戻す -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.Fibration

private theorem normalize_two_isos {D : Type v} [Category.{w} D]
    {a b c d e f : D} (s : a ≅ b) (t : b ≅ c) (s' : d ≅ e) (t' : e ≅ f)
    (α : a ⟶ d) (β : b ⟶ e) (γ : c ⟶ f)
    (h₀ : s.inv ≫ α ≫ s'.hom = β) (h₁ : t.inv ≫ β ≫ t'.hom = γ) :
    (s ≪≫ t).inv ≫ α ≫ (s' ≪≫ t').hom = γ := by
  calc
    _ = t.inv ≫ (s.inv ≫ α ≫ s'.hom) ≫ t'.hom := by
      simp only [Iso.trans_inv, Iso.trans_hom, Category.assoc]
    _ = γ := by rw [h₀, h₁]

variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  (h : IsVerdierSequence i q) (x : B.obj _⦋0⦌) (c : TransportSimplexCategory B.obj)

/-- 同じ coslice 図式の商上の値を、元の同じ strict Kan 値へ戻す実制限同型。 -/
def fractionKanQuotientDiagram_initialVertexIso :
    VertexIso ((fractionKanQuotientDiagram h x).app (Opposite.op ⦋0⦌)
      (ULift.up (q.hom.app (Opposite.op ⦋0⦌)
        ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌) (nerveVertex c)))))
      (spaceInfinityVertex ((fractionSimplexKanMappingDiagram q.hom x).obj c)) :=
  (fractionKanQuotientDiagram_restrictionIso h x).app
    (ULift.up ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌) (nerveVertex c))) ≪≫
      fractionKanSpaceDiagram_initialVertexIso q.hom x c

/-- 同じ自然変換の実評価辺の両端を、元の同じ Kan 値の標準頂点へ揃える。 -/
def weakSpanKanComparisonValueEdge :
    SpaceInfinity.Edge (spaceInfinityVertex ((weakSpanKanDiagram i x).obj c))
      (spaceInfinityVertex ((fractionSimplexKanMappingDiagram q.hom x).obj c)) :=
  (functorEdgeAt (weakSpanKanMappingComparisonEdge h x) (ULift.up (nerveVertex c))).ofEq
    (kanDiagramCoherentNerve_vertex (weakSpanKanDiagram i x) c)
    (kanDiagramCoherentNerve_vertex (fractionSimplexKanMappingDiagram q.hom x) c)

/-- 端点表示を揃えても、辺の一単体は元の同じ strict Kan 比較成分の coherent な辺そのもの。 -/
theorem weakSpanKanComparisonValueEdge_edge : (weakSpanKanComparisonValueEdge h x c).edge =
    (coherentNerveEdge (show (weakSpanKanDiagram i x).obj c ⟶
      (fractionSimplexKanMappingDiagram q.hom x).obj c from
        (weakSpanKanMappingComparison h x).app c)).edge :=
  kanDiagramNaturalTransformationEdge_at
    (F := ⟨weakSpanKanDiagram i x, trivial⟩)
    (G := ⟨fractionSimplexKanMappingDiagram q.hom x, trivial⟩)
    (Functor.whiskerRight (weakSpanKanMappingComparison h x) kanObjectForget) c

/-- 元の商上の比較の成分は、同じ実値同型で正規化すると元の strict Kan 比較成分の類。 -/
theorem weakQuotientMappingComparison_native_component :
    (weakSpanKanQuotientDiagram_initialVertexIso h x c).inv ≫
      functorHomEvaluate (weakQuotientMappingComparison h x)
        (ULift.up (q.hom.app (Opposite.op ⦋0⦌)
          ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌) (nerveVertex c)))) ≫
      (fractionKanQuotientDiagram_initialVertexIso h x c).hom =
      Truncated.HomotopyCategory.homMk (weakSpanKanComparisonValueEdge h x c).toTruncated := by
  let y := (transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌) (nerveVertex c)
  let z := ULift.up.{u + 1} (nerveVertex c)
  let s := (weakSpanKanQuotientDiagram_restrictionIso h x).app (ULift.up y)
  let t := (weakSpanKanSpaceDiagram_restrictionIso i x).app z
  let s' := (fractionKanQuotientDiagram_restrictionIso h x).app (ULift.up y)
  let t' := (fractionKanSpaceDiagram_restrictionIso q.hom x).app z
  let v := eqToIso (congrArg HomotopyCategory.mk
    (kanDiagramCoherentNerve_vertex (weakSpanKanDiagram i x) c))
  let v' := eqToIso (congrArg HomotopyCategory.mk
    (kanDiagramCoherentNerve_vertex (fractionSimplexKanMappingDiagram q.hom x) c))
  let α := functorHomEvaluate (weakQuotientMappingComparison h x)
    (ULift.up (q.hom.app (Opposite.op ⦋0⦌) y))
  let β := functorHomEvaluate (weakSpanSpaceMappingComparison h x) (ULift.up y)
  let γ := functorHomEvaluate (Truncated.HomotopyCategory.homMk
    (weakSpanKanMappingComparisonEdge h x).toTruncated) z
  let δ := Truncated.HomotopyCategory.homMk (weakSpanKanComparisonValueEdge h x c).toTruncated
  have h₀ : s.inv ≫ α ≫ s'.hom = β :=
    weakQuotientMappingComparison_component_restriction h x y
  have h₁ : t.inv ≫ β ≫ t'.hom = γ :=
    weakSpanSpaceMappingComparison_component_restriction h x c
  have h₂ : v.inv ≫ γ ≫ v'.hom = δ := by
    have he := functorHomEvaluate_edge_hom (weakSpanKanMappingComparisonEdge h x) z
    have ht := homMk_transport
      (kanDiagramCoherentNerve_vertex (weakSpanKanDiagram i x) c)
      (kanDiagramCoherentNerve_vertex (fractionSimplexKanMappingDiagram q.hom x) c)
      (functorEdgeAt (weakSpanKanMappingComparisonEdge h x) z).toTruncated
      (weakSpanKanComparisonValueEdge h x c).toTruncated rfl
    exact (congrArg (fun m => v.inv ≫ m ≫ v'.hom) he).trans ht
  exact normalize_two_isos s (t ≪≫ v) s' (t' ≪≫ v') α β δ h₀
    (normalize_two_isos t v t' v' β γ δ h₁ h₂)

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanQuotientDiagram_initialVertexIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fractionKanQuotientDiagram_initialVertexIso := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanQuotientDiagram_initialVertexIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakQuotientMappingComparison_native_component := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientMappingComparison_native_component

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanComparisonValueEdge (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanComparisonValueEdge := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanComparisonValueEdge

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanComparisonValueEdge_edge := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanComparisonValueEdge_edge

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fractionKanQuotientDiagram_initialVertexIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionKanQuotientDiagram_initialVertexIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanComparisonValueEdge._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanComparisonValueEdge._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanComparisonValueEdge._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanComparisonValueEdge._proof_2
