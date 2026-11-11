module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionEvaluationLifting

/-!
概要：固定 span の余錐比較から suspension の普遍四角形と厳密切断を構成する。
方針：実 fiber の同型で始対象性を余極限性へ戻し、全境界持ち上げを使う。
規約：安定性・有限余極限は仮定しない。使われ方：一般安定性判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 同じ固定 span の普遍性と suspension の全単体構成。 -/
lemma suspensionDiagramEvaluation_source_trivialKanFibration_of_squares (X : SSet.{u})
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex X]
    (h : ∀ x : X _⦋0⦌, Nonempty (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 0 0) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro a b sq
  cases n with
  | zero =>
    let q := Classical.choice (h (SSet.yonedaEquiv b))
    let v := q.diagramVertex
    have hv : (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 0 0).app (Opposite.op ⦋0⦌) v =
        SSet.yonedaEquiv b := (q.diagramVertex_evaluation 0 0).trans q.source_eq
    refine CommSq.HasLift.mk' {
      l := SSet.yonedaEquiv.symm v
      fac_left := boundary.hom_ext₀
      fac_right := ?_ }
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, hv]
  | succ n =>
    let ι := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X)
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsSuspensionDiagramVertex).ι
    let j := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (Δ[1] : SSet.{u})).obj X) _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroTargetArrow).ι
    have hBL : CommSq (a ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.suspensionDiagramBottomArrow X) (boundary (n + 1)).ι
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.zeroTargetArrowSource X) b := by
      constructor
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.suspensionDiagramBottomArrow_source]
      exact sq.w
    have hBR : CommSq (a ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.suspensionDiagramLeftArrow X) (boundary (n + 1)).ι
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.zeroTargetArrowSource X) b := by
      constructor
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.suspensionDiagramLeftArrow_source]
      exact sq.w
    have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.zeroTargetArrowSource X)
      (boundary (n + 1)).ι inferInstance
    let L := hBL.lift
    let R := hBR.lift
    have hLR : (L ≫ j) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
        (R ≫ j) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) :=
      hBL.fac_right.trans hBR.fac_right.symm
    let d := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_spanFamilyOfArrows (L ≫ j) (R ≫ j) hLR
    have hd : (boundary (n + 1)).ι ≫ d = a ≫ ι ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary).app X := by
      apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_spanFamily_hom_ext
      · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_spanFamilyOfArrows_left]
        rw [← Category.assoc, hBL.fac_left, Category.assoc]
        rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.suspensionDiagramBottomArrow, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι]
        simp only [Category.assoc, ← NatTrans.comp_app, ← pre_map, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_bottomEdge]
        rfl
      · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_spanFamilyOfArrows_right]
        rw [← Category.assoc, hBR.fac_left, Category.assoc]
        rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.suspensionDiagramLeftArrow, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι]
        simp only [Category.assoc, ← NatTrans.comp_app, ← pre_map, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_leftEdge]
        rfl
    let c := a ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.suspensionDiagramCoconeFamily X
    have hcd : CommSq c (boundary (n + 1)).ι
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCoconeProjection (horn 2 0 : SSet.{u}) X) d := by
      constructor
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.suspensionDiagramCoconeFamily_projection]
      exact hd.symm
    have : HasLiftingProperty (boundary (n + 1)).ι
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCoconeProjection (horn 2 0 : SSet.{u}) X) :=
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.relativeInitialProjection_hasLiftingProperty_boundary
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction (horn 2 0 : SSet.{u}) X) n
    let U := hcd.lift
    let k := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.relativeInitialVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction (horn 2 0 : SSet.{u}) X)).ι
    let F := U ≫ k ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.inv).app X
    have hFa : (boundary (n + 1)).ι ≫ F = a ≫ ι := by
      dsimp only [F]
      rw [← Category.assoc, ← Category.assoc, hcd.fac_left, Category.assoc]
      change a ≫ (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.suspensionDiagramCoconeFamily X ≫ k) ≫
        (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.inv).app X = _
      rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.suspensionDiagramCoconeFamily_ι]
      simp only [Category.assoc, ← NatTrans.comp_app, ← pre_map, Iso.inv_hom_id,
        pre_id, NatTrans.id_app, Category.comp_id]
      rfl
    have hv (v : (Δ[n + 1] : SSet.{u}) _⦋0⦌) :
        _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsSuspensionDiagramVertex (F.app (Opposite.op ⦋0⦌) v) := by
      let w : (boundary (n + 1) : SSet.{u}) _⦋0⦌ := ⟨v, by
        have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary.{u} n (stdSimplex.obj₀Equiv.{u} v)
        rw [Equiv.symm_apply_apply] at h
        exact h⟩
      have he := ConcreteCategory.congr_hom (NatTrans.congr_app hFa (Opposite.op ⦋0⦌)) w
      change F.app (Opposite.op ⦋0⦌) v = (a.app (Opposite.op ⦋0⦌) w).val at he
      rw [he]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (a.app (Opposite.op ⦋0⦌) w)
    let g := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsSuspensionDiagramVertex F hv
    have hg : g ≫ ι = F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _
    refine CommSq.HasLift.mk' { l := g, fac_left := ?_, fac_right := ?_ }
    · apply (cancel_mono ι).1
      rw [Category.assoc, hg, hFa]
    · change g ≫ ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2), stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = b
      rw [← Category.assoc, hg]
      have hFd : F ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary).app X = d := by
        dsimp only [F]
        simp only [Category.assoc, ← NatTrans.comp_app, ← pre_map]
        have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.inv =
            _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (horn 2 0 : SSet.{u}) Δ[0] := by
          simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary, Category.assoc, Iso.hom_inv_id, Category.comp_id]
        rw [hi]
        exact hcd.fac_right
      have hFL : F ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge).app X = L ≫ j := by
        have hh := congrArg (fun t ↦ t ≫ (pre horn₂₀.ι₀₁).app X) hFd
        rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_spanFamilyOfArrows_left] at hh
        simpa only [Category.assoc, ← NatTrans.comp_app, ← pre_map,
          _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_bottomEdge] using hh
      have hh := congrArg
        (fun t ↦ t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) hFL
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt] at hh
      exact hh.trans hBL.fac_right
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
