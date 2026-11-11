module
public import SerrePositivity.KST.SConstruction.PerfectLaxQuotientRectangle

/-! # 比較長方形の全単体を保つ Cat^perf への持ち上げ
概要：元の比較道と二面・両合成三角形を持つ長方形を、全体として持ち上げる。
方針：六頂点を左右の既存正方形に帰着し、完備対象の全部分複体へ持ち上げる。
規約：面ごとに充填を選び直さない。使われ方：同じ長方形の二面と外周の fiber 性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories LocalizingInvariants
open scoped Simplicial
namespace PerfectLaxQuotient
variable {C D B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D B}
  (d : PerfectLaxQuotient p q)

/-- 元の長方形の六頂点は、左右の同じ完備正方形の頂点である。 -/
lemma rawRectangle_vertex_complete
    (x : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) _⦋0⦌) :
    perfectStableVertexPredicate (d.rawRectangle.diagram.app (Opposite.op ⦋0⦌) x) := by
  obtain ⟨x, y⟩ := x
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective y
  fin_cases i
  · change perfectStableVertexPredicate ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare d.rawRectangle.diagram 2).app _
      (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm j))
    rw [d.rawRectangle.left_eq]
    exact d.universalRawSquare_vertex_complete _
  · change perfectStableVertexPredicate ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare d.rawRectangle.diagram 2).app _
      (stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm j))
    rw [d.rawRectangle.left_eq]
    exact d.universalRawSquare_vertex_complete _
  · change perfectStableVertexPredicate ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare d.rawRectangle.diagram 0).app _
      (stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm j))
    rw [d.rawRectangle.right_eq]
    exact perfectVerdierRawSquare_vertex_complete
      (perfectIdentityLaxSequence d.sequence.right d.sequence.right_complete) _

/-- 元の二面・両合成三角形を全て保持する Cat^perf の実長方形。 -/
def rectangleDiagram : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ perfectStableInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift perfectStableVertexPredicate d.rawRectangle.diagram
    d.rawRectangle_vertex_complete

/-- 持ち上げた長方形の包含後は、元の全長方形を厳密に回収する。 -/
lemma rectangleDiagram_inclusion :
    d.rectangleDiagram ≫ perfectStableInfinityInclusion = d.rawRectangle.diagram :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

/-- 同じ Cat^perf 長方形の左面は、元の指定比較正方形そのもの。 -/
lemma rectangleDiagram_left : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare d.rectangleDiagram 2 =
    (β_ (Δ[1] : SSet.{u + 1}) Δ[1]).hom ≫ d.universalSquare := by
  apply (cancel_mono perfectStableInfinityInclusion).mp
  change _ ≫ (d.rectangleDiagram ≫ perfectStableInfinityInclusion) =
    (β_ (Δ[1] : SSet.{u + 1}) Δ[1]).hom ≫
      (d.universalSquare ≫ perfectStableInfinityInclusion)
  rw [d.rectangleDiagram_inclusion, d.universalSquare_inclusion]
  exact d.rawRectangle.left_eq

/-- 同じ Cat^perf 長方形の右面は、元の恒等 lax 差の提示正方形。 -/
lemma rectangleDiagram_right : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare d.rectangleDiagram 0 =
    (β_ (Δ[1] : SSet.{u + 1}) Δ[1]).hom ≫
      (perfectIdentityLaxSequence d.sequence.right
        d.sequence.right_complete).presentation.square := by
  apply (cancel_mono perfectStableInfinityInclusion).mp
  change _ ≫ (d.rectangleDiagram ≫ perfectStableInfinityInclusion) =
    (β_ (Δ[1] : SSet.{u + 1}) Δ[1]).hom ≫
      (perfectVerdierSquare _ ≫ perfectStableInfinityInclusion)
  rw [d.rectangleDiagram_inclusion, perfectVerdierSquare_inclusion]
  exact d.rawRectangle.right_eq

end PerfectLaxQuotient
end SerrePositivity.KST.SConstruction
