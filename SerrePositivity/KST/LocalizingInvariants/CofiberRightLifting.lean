module
public import SerrePositivity.KST.LocalizingInvariants.CofiberDiagramChoices

/-!
概要：安定圏の普遍 cofiber 四角形の右辺評価は trivial Kan fibration。
方針：元の右辺を保ち、零始点の上辺と普遍錐を境界に沿って充填する。
規約：引き戻しを元の cofiber 図式へ安定性で戻す。使われ方：cofiber 回転の完全性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams

/- 右辺を固定したまま全境界を持ち上げる。 -/
instance right_trivialKanFibration (X : SSet.{u})
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.right X) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro a b sq
  cases n with
  | zero =>
    obtain ⟨v, hv⟩ := right_surjective X (SSet.yonedaEquiv b)
    refine CommSq.HasLift.mk' {
      l := SSet.yonedaEquiv.symm v
      fac_left := boundary.hom_ext₀
      fac_right := ?_ }
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, hv]
  | succ n =>
    let ι := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X)
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.Predicate).ι
    let j := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (Δ[1] : SSet.{u})).obj X) _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroSourceArrow).ι
    have hBR : CommSq (a ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.top X) (boundary (n + 1)).ι
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourceArrowTarget X)
        (b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
      constructor
      rw [Category.assoc, ← right_target, ← Category.assoc, sq.w, Category.assoc]
    have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourceArrowTarget X)
      (boundary (n + 1)).ι inferInstance
    let R := hBR.lift
    have hLR : b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
        (R ≫ j) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) :=
      hBR.fac_right.symm
    let d := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_cospanFamilyOfArrows b (R ≫ j) hLR
    have hd : (boundary (n + 1)).ι ≫ d = a ≫ ι ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary).app X := by
      apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_cospanFamily_hom_ext
      · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_cospanFamilyOfArrows_left]
        simp only [Category.assoc, ← NatTrans.comp_app, ← pre_map,
          _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_rightEdge]
        change (boundary (n + 1)).ι ≫ b = a ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.right X
        exact sq.w.symm
      · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_cospanFamilyOfArrows_right]
        rw [← Category.assoc, hBR.fac_left, Category.assoc]
        rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.top, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι]
        simp only [Category.assoc, ← NatTrans.comp_app, ← pre_map, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_topEdge]
        rfl
    let c := a ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.cones X
    have hcd : CommSq c (boundary (n + 1)).ι
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitConeProjection (horn 2 2 : SSet.{u}) X) d := by
      constructor
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.cones_projection]
      exact hd.symm
    have : HasLiftingProperty (boundary (n + 1)).ι
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitConeProjection (horn 2 2 : SSet.{u}) X) :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeTerminalProjection_hasLiftingProperty_boundary
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction (horn 2 2 : SSet.{u}) X) n
    let U := hcd.lift
    let k := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeTerminalVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction (horn 2 2 : SSet.{u}) X)).ι
    let F := U ≫ k ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.inv).app X
    have hFa : (boundary (n + 1)).ι ≫ F = a ≫ ι := by
      dsimp only [F]
      rw [← Category.assoc, ← Category.assoc, hcd.fac_left, Category.assoc]
      change a ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.cones X ≫ k) ≫
        (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.inv).app X = _
      rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.cones_inclusion]
      simp only [Category.assoc, ← NatTrans.comp_app, ← pre_map, Iso.inv_hom_id,
        pre_id, NatTrans.id_app, Category.comp_id]
      rfl
    have hv (v : (Δ[n + 1] : SSet.{u}) _⦋0⦌) :
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.Predicate (F.app (Opposite.op ⦋0⦌) v) := by
      let w : (boundary (n + 1) : SSet.{u}) _⦋0⦌ := ⟨v, by
        have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary.{u} n (stdSimplex.obj₀Equiv.{u} v)
        rw [Equiv.symm_apply_apply] at h
        exact h⟩
      have he := ConcreteCategory.congr_hom (NatTrans.congr_app hFa (Opposite.op ⦋0⦌)) w
      change F.app (Opposite.op ⦋0⦌) v = (a.app (Opposite.op ⦋0⦌) w).val at he
      rw [he]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (a.app (Opposite.op ⦋0⦌) w)
    let g := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.Predicate F hv
    have hg : g ≫ ι = F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _
    refine CommSq.HasLift.mk' { l := g, fac_left := ?_, fac_right := ?_ }
    · apply (cancel_mono ι).1
      rw [Category.assoc, hg, hFa]
    · change g ≫ ι ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge).app X = b
      rw [← Category.assoc, hg]
      have hFd : F ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary).app X = d := by
        dsimp only [F]
        simp only [Category.assoc, ← NatTrans.comp_app, ← pre_map]
        have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.inv =
            _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] (horn 2 2 : SSet.{u}) := by
          simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary, Category.assoc, Iso.hom_inv_id, Category.comp_id]
        rw [hi]
        exact hcd.fac_right
      have hFL : F ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge).app X = b := by
        have hh := congrArg (fun t ↦ t ≫ (pre horn₂₂.ι₀₂).app X) hFd
        rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_cospanFamilyOfArrows_left] at hh
        simpa only [Category.assoc, ← NatTrans.comp_app, ← pre_map,
          _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_rightEdge] using hh
      exact hFL

end SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams
