module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions
open _root_.SerrePositivity.KST.LocalizingInvariants

variable {K X : SSet.{u}} {b : K ⟶ X}

/-- 同じ指定商全錐の頂点の点写像。 -/
def quotientConeCoslicePoint (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone b) : (Δ[0] : SSet.{u}) ⟶ X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] K ≫ t.val

/-- 指定商全錐を、同じ頂点の coslice 内の全図式へ戻す。 -/
def quotientConeCosliceDiagram (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone b) : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.quotientConeCoslicePoint t) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry t.val rfl

lemma quotientConeCosliceDiagram_projection (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone b) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.quotientConeCosliceDiagram t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.quotientConeCoslicePoint t) = b := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.quotientConeCosliceDiagram, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderCurry_projection]
  exact t.property

lemma quotientConeCosliceDiagram_uncurry (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.quotientConeCosliceDiagram t) = t.val := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_curry _ _

/-- 元の指定商全錐から、全指定辺の実分数と同じ共通実全錐を回収する。 -/
lemma exists_verdierFiniteQuotientConeSpanFamily {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C} (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)
    {J : Type u} [Finite J] {K : SSet.{u}} [K.Finite]
    (p : K ⟶ B.obj) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (p ≫ q.hom)) (k₀ k₁ : J → K _⦋0⦌)
    (e : ∀ j : J, Truncated.Edge
      (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.quotientConeCoslicePoint t)))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.quotientConeCosliceDiagram t).app (Opposite.op ⦋0⦌) (k₀ j))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.quotientConeCosliceDiagram t).app (Opposite.op ⦋0⦌) (k₁ j))) :
    ∃ r : ∀ j : J, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCosliceFractionNormalization h (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.quotientConeCoslicePoint t) (e j)
        (p.app (Opposite.op ⦋0⦌) (k₀ j)) (p.app (Opposite.op ⦋0⦌) (k₁ j)),
      ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone
          (finiteCosliceSpanNativeDiagram p (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.quotientConeCosliceDiagram t) k₀ k₁ r),
        ∃ _iso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
          (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver
            (finiteCosliceSpanNativeDiagram p (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.quotientConeCosliceDiagram t) k₀ k₁ r ≫ q.hom))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone q.hom c)
          (finiteCosliceSpanQuotientCone p (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.quotientConeCosliceDiagram t) k₀ k₁ r
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.quotientConeCosliceDiagram_projection t)),
          ∀ k : (finiteFractionAttachmentShape k₀ k₁) _⦋0⦌,
            _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := C.obj) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg
              (finiteCosliceSpanQuotientCone p (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.quotientConeCosliceDiagram t) k₀ k₁ r
                (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.quotientConeCosliceDiagram_projection t)) k) →
            (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg c k).edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i :=
  exists_verdierFiniteCosliceSpanFamilyAttachment (h := h) (e := e)
    p (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.quotientConeCosliceDiagram t) k₀ k₁ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.quotientConeCosliceDiagram_projection t)

/-- 添付後も元の指定商全錐は、同じ全錐の制限として厳密に保持される。 -/
lemma finiteQuotientConeSpan_original {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C} {h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q}
    {J : Type u} {K : SSet.{u}} (p : K ⟶ B.obj) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (p ≫ q.hom))
    (k₀ k₁ : J → K _⦋0⦌)
    {e : ∀ j : J, Truncated.Edge
      (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.quotientConeCoslicePoint t)))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.quotientConeCosliceDiagram t).app (Opposite.op ⦋0⦌) (k₀ j))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.quotientConeCosliceDiagram t).app (Opposite.op ⦋0⦌) (k₁ j))}
    (r : ∀ j : J, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCosliceFractionNormalization h (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.quotientConeCoslicePoint t) (e j)
      (p.app (Opposite.op ⦋0⦌) (k₀ j)) (p.app (Opposite.op ⦋0⦌) (k₁ j))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u}))
        (pushout.inl (finiteFractionDiagramTargets k₀ k₁) finiteFractionSpanTargets) ≫
      (finiteCosliceSpanQuotientCone p (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.quotientConeCosliceDiagram t) k₀ k₁ r
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.quotientConeCosliceDiagram_projection t)).val = t.val := by
  rw [finiteCosliceSpanQuotientCone_original, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.quotientConeCosliceDiagram_uncurry]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
