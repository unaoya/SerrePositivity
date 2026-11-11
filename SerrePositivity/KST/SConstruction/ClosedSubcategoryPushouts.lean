module
public import SerrePositivity.KST.SConstruction.ClosedStablePredicate
public import SerrePositivity.KST.SConstruction.DiagramPushoutChoice

/-! # 閉じた全部分圏の押し出しの存在と保存
概要：周囲の押し出しに閉じた全部分圏では、同じ span の押し出しを内部に戻せる。
方針：周囲の普遍四角形を全頂点の閉性で持ち上げ、一意性で任意の内部の押し出しを比較する。
規約：内部の安定性は仮定しない。使われ方：閉性からの安定性の証明。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 同じ span を持つ二つの四角形の下辺は等しい。 -/
lemma squareBottomEdge_eq_of_pushoutSpan_eq {X : SSet.{u}}
    {R S : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X} (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan R = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan S) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ R = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ S := by
  have he := congrArg (fun p => horn₂₀.ι₀₁ ≫ p) h
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_bottomEdge] using he

/-- 同じ span を持つ二つの四角形の左辺は等しい。 -/
lemma squareLeftEdge_eq_of_pushoutSpan_eq {X : SSet.{u}}
    {R S : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X} (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan R = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan S) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ R = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ S := by
  have he := congrArg (fun p => horn₂₀.ι₀₂ ≫ p) h
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_leftEdge] using he

/-- 周囲で同じ span を持つ四角形の最初の三つの角は頂点条件を満たす。 -/
lemma square_initial_corners_of_span {X : StableModel.{u}} (P : ClosedStablePredicate X)
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ closedSubcategory P)
    (R : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X.carrier)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan R = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (F ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ P.predicate).ι)) :
    P.predicate (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex R 0 0) ∧ P.predicate (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex R 1 0) ∧
      P.predicate (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex R 0 1) := by
  have hb (i : Fin 2) : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex R i 0 =
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F i 0).val :=
    ConcreteCategory.congr_hom
      (NatTrans.congr_app (squareBottomEdge_eq_of_pushoutSpan_eq h) (Opposite.op ⦋0⦌))
      (stdSimplex.obj₀Equiv.symm i)
  have hl : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex R 0 1 = (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 0 1).val :=
    ConcreteCategory.congr_hom
      (NatTrans.congr_app (squareLeftEdge_eq_of_pushoutSpan_eq h) (Opposite.op ⦋0⦌))
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2))
  exact ⟨(hb 0).symm ▸ closedSubcategory_vertex P _,
    (hb 1).symm ▸ closedSubcategory_vertex P _, hl.symm ▸ closedSubcategory_vertex P _⟩

/-- 任意の内部の span は周囲でも普遍な内部の押し出し四角形へ補完できる。 -/
lemma exists_closedSubcategory_pushoutSquare {X : StableModel.{u}} (P : ClosedStablePredicate X)
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ closedSubcategory P) :
    ∃ D : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ closedSubcategory P,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan D = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan F ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare D ∧
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (D ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ P.predicate).ι) := by
  let i := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ P.predicate).ι
  obtain ⟨R, hR, hRp⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_stable_pushoutSquare_of_span (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (F ≫ i))
  have hc := square_initial_corners_of_span P F R hR
  have hv := square_vertices_of_corners P.predicate R hc.1 hc.2.1 hc.2.2
    (P.pushout_mem R hRp hc.1 hc.2.1 hc.2.2)
  let D := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift P.predicate R hv
  have hDi : D ≫ i = R := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _
  have hDs : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan D = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan F := by
    apply (cancel_mono i).1
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary ≫ D ≫ i = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary ≫ F ≫ i
    rw [hDi]
    exact hR
  have hDp : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (D ≫ i) := hDi.symm ▸ hRp
  exact ⟨D, hDs, isPushoutSquare_fullSubcomplex_of_ambient P.predicate D hDp, hDp⟩

/-- 閉じた全部分圏の包含は全ての内部の押し出しを保つ。 -/
lemma closedSubcategoryInclusion_preservesPushout {X : StableModel.{u}}
    (P : ClosedStablePredicate X)
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ closedSubcategory P) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (F ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ P.predicate).ι) := by
  obtain ⟨D, hDs, hD, hDi⟩ := exists_closedSubcategory_pushoutSquare P F
  let e := pushoutSquareIsoOfSpanIso D F hD hF (by rw [hDs])
  exact IsPushoutSquare.of_functorIso hDi (e.postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ P.predicate).ι)

end SerrePositivity.KST.SConstruction
