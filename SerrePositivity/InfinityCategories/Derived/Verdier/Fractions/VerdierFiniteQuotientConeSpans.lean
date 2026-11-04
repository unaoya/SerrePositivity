module

public import SerrePositivity.KST.LocalizingInvariants.FiniteCosliceSpanAttachment

/-!
概要：元の指定商全錐から、有限個の指定辺の実分数と共通実全錐を一括回収する。
方針：商全錐を同じ頂点の coslice 図式へ curry し、有限同時添付を実適用する。
規約：coslice 図式や各実分母を新しい未供給入力にしない。
使われ方：完成側有限境界の正規化における、同じ全図式と共有始点の保持。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants

variable {K X : SSet.{u}} {b : K ⟶ X}

/-- 同じ指定商全錐の頂点の点写像。 -/
def quotientConeCoslicePoint (t : JoinCone b) : (Δ[0] : SSet.{u}) ⟶ X :=
  joinInl Δ[0] K ≫ t.val

/-- 指定商全錐を、同じ頂点の coslice 内の全図式へ戻す。 -/
def quotientConeCosliceDiagram (t : JoinCone b) : K ⟶ sliceUnder (quotientConeCoslicePoint t) :=
  sliceUnderCurry t.val rfl

lemma quotientConeCosliceDiagram_projection (t : JoinCone b) :
    quotientConeCosliceDiagram t ≫ sliceUnderProjection (quotientConeCoslicePoint t) = b := by
  rw [quotientConeCosliceDiagram, sliceUnderCurry_projection]
  exact t.property

lemma quotientConeCosliceDiagram_uncurry (t : JoinCone b) :
    sliceUnderUncurry (quotientConeCosliceDiagram t) = t.val := sliceUnderUncurry_curry _ _

/-- 元の指定商全錐から、全指定辺の実分数と同じ共通実全錐を回収する。 -/
lemma exists_verdierFiniteQuotientConeSpanFamily {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    {J : Type u} [Finite J] {K : SSet.{u}} [K.Finite]
    (p : K ⟶ B.obj) (t : JoinCone (p ≫ q.hom)) (k₀ k₁ : J → K _⦋0⦌)
    (e : ∀ j : J, Truncated.Edge
      (X := (truncation 2).obj (sliceUnder (quotientConeCoslicePoint t)))
      ((quotientConeCosliceDiagram t).app (Opposite.op ⦋0⦌) (k₀ j))
      ((quotientConeCosliceDiagram t).app (Opposite.op ⦋0⦌) (k₁ j))) :
    ∃ r : ∀ j : J, VerdierCosliceFractionNormalization h (quotientConeCoslicePoint t) (e j)
        (p.app (Opposite.op ⦋0⦌) (k₀ j)) (p.app (Opposite.op ⦋0⦌) (k₁ j)),
      ∃ c : JoinCone
          (finiteCosliceSpanNativeDiagram p (quotientConeCosliceDiagram t) k₀ k₁ r),
        ∃ _iso : VertexIso
          (X := sliceOver
            (finiteCosliceSpanNativeDiagram p (quotientConeCosliceDiagram t) k₀ k₁ r ≫ q.hom))
          (mapJoinCone q.hom c)
          (finiteCosliceSpanQuotientCone p (quotientConeCosliceDiagram t) k₀ k₁ r
            (quotientConeCosliceDiagram_projection t)),
          ∀ k : (finiteFractionAttachmentShape k₀ k₁) _⦋0⦌,
            IsInvertibleEdge (X := C.obj) (F2.nativeConeLeg
              (finiteCosliceSpanQuotientCone p (quotientConeCosliceDiagram t) k₀ k₁ r
                (quotientConeCosliceDiagram_projection t)) k) →
            (F2.nativeConeLeg c k).edge ∈ weakEquivalences i :=
  exists_verdierFiniteCosliceSpanFamilyAttachment (h := h) (e := e)
    p (quotientConeCosliceDiagram t) k₀ k₁ (quotientConeCosliceDiagram_projection t)

/-- 添付後も元の指定商全錐は、同じ全錐の制限として厳密に保持される。 -/
lemma finiteQuotientConeSpan_original {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} {h : IsVerdierSequence i q}
    {J : Type u} {K : SSet.{u}} (p : K ⟶ B.obj) (t : JoinCone (p ≫ q.hom))
    (k₀ k₁ : J → K _⦋0⦌)
    {e : ∀ j : J, Truncated.Edge
      (X := (truncation 2).obj (sliceUnder (quotientConeCoslicePoint t)))
      ((quotientConeCosliceDiagram t).app (Opposite.op ⦋0⦌) (k₀ j))
      ((quotientConeCosliceDiagram t).app (Opposite.op ⦋0⦌) (k₁ j))}
    (r : ∀ j : J, VerdierCosliceFractionNormalization h (quotientConeCoslicePoint t) (e j)
      (p.app (Opposite.op ⦋0⦌) (k₀ j)) (p.app (Opposite.op ⦋0⦌) (k₁ j))) :
    joinMap (𝟙 (Δ[0] : SSet.{u}))
        (pushout.inl (finiteFractionDiagramTargets k₀ k₁) finiteFractionSpanTargets) ≫
      (finiteCosliceSpanQuotientCone p (quotientConeCosliceDiagram t) k₀ k₁ r
        (quotientConeCosliceDiagram_projection t)).val = t.val := by
  rw [finiteCosliceSpanQuotientCone_original, quotientConeCosliceDiagram_uncurry]

end SerrePositivity.KST.LocalizingInvariants
