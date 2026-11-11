module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SquareFixedSpanCocone

/-!
概要：元の loop 四角形の押し出し性と、全 suspension/loop 図式の比較。
方針：同じ指定点の始対象性を実固定 span へ戻し、全図式の評価を比較する。
規約：安定性は仮定しない。使われ方：HA 1.4.2.27 の一般安定性判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 同じ実四角形と全単体の図式を保つ普遍性の比較。 -/
def squareFixedSpanVertex {X : SSet.{u}} (F : Δ[1] ⊗ Δ[1] ⟶ X) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan F))) _⦋0⦌ :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F, by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan F) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant _ 0
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]⟩

/-- 同じ実四角形と全単体の図式を保つ普遍性の比較。 -/
lemma squareFixedSpanCoconeIso_vertex {X : SSet.{u}} (F : Δ[1] ⊗ Δ[1] ⟶ X) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareFixedSpanCoconeIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan F)).hom.app (Opposite.op ⦋0⦌)
      (squareFixedSpanVertex F) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeFamilyVertexEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan F) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone F) := by
  apply Subtype.ext
  rfl

/-- 同じ実四角形と全単体の図式を保つ普遍性の比較。 -/
lemma squareFixedSpanVertex_isInitial_iff {X : SSet.{u}} [Quasicategory X]
    (F : Δ[1] ⊗ Δ[1] ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (squareFixedSpanVertex F) ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare F := by
  have : Quasicategory
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan F))) :=
    quasicategory_of_innerFibration (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareFixedSpanCoconeIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan F)).hom
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareFixedSpanCoconeIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan F))
  have h := e.isInitialVertex_iff (squareFixedSpanVertex F)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (squareFixedSpanVertex F) ↔
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareFixedSpanCoconeIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan F)).hom.app
      (Opposite.op ⦋0⦌) (squareFixedSpanVertex F)) at h
  rw [squareFixedSpanCoconeIso_vertex] at h
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_isInitialVertex_coconeFamily (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone F)).symm

/-- 同じ実四角形と全単体の図式を保つ普遍性の比較。 -/
lemma squareFixedSpan_isPushout_of_initial {X : SSet.{u}} [Quasicategory X]
    {b : ((ihom (horn 2 0 : SSet.{u})).obj X) _⦋0⦌}
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary).app X) b) _⦋0⦌)
    (hv : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex v) (F : Δ[1] ⊗ Δ[1] ⟶ X)
    (hF : v.val = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare F := by
  have hb : b = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan F) := by
    exact (v.property.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero b)).symm.trans
      (congrArg (((pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary).app X).app (Opposite.op ⦋0⦌)) hF)
  subst b
  have he : v = squareFixedSpanVertex F := Subtype.ext hF
  rw [he] at hv
  exact (squareFixedSpanVertex_isInitial_iff F).mp hv

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
