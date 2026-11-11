module

public import SerrePositivity.KST.Spectra.SpectrumLoopSquares
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopDiagramArrows

/-!
概要：Sp の loop 図式の終点評価は安定性を仮定せず trivial Kan fibration。
方針：零次元は構成済みの loop 四角形、正次元は零始点の辺と普遍錐の相対境界充填。
規約：実際の全単体の図式を扱う。使われ方：native loop 関手の構成と選択の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum

/-- 実際の Sp の loop 図式の終点評価は頂点上全射。 -/
lemma nativeLoopTarget_surjective :
    Function.Surjective ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 1 1).app (Opposite.op ⦋0⦌)) := by
  intro x
  refine ⟨(loopSquare x).diagramVertex, ?_⟩
  exact ((loopSquare x).diagramVertex_evaluation 1 1).trans (loopSquare x).target_eq

/-- 全境界の持ち上げを持つ Sp の loop 図式の終点評価。 -/
instance nativeLoopTarget_trivialKanFibration :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 1 1) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro a b sq
  cases n with
  | zero =>
    obtain ⟨v, hv⟩ := nativeLoopTarget_surjective (SSet.yonedaEquiv b)
    refine CommSq.HasLift.mk' {
      l := SSet.yonedaEquiv.symm v
      fac_left := boundary.hom_ext₀
      fac_right := ?_ }
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, hv]
  | succ n =>
    let ι := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u + 1})).obj (Sp.{u}))
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι
    let j := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices
      ((ihom (Δ[1] : SSet.{u + 1})).obj Sp.{u}) _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroSourceArrow).ι
    have hBL : CommSq (a ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramRightArrow (Sp.{u})) (boundary (n + 1)).ι
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourceArrowTarget (Sp.{u})) b := by
      constructor
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramRightArrow_target]
      exact sq.w
    have hBR : CommSq (a ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramTopArrow (Sp.{u})) (boundary (n + 1)).ι
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourceArrowTarget (Sp.{u})) b := by
      constructor
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramTopArrow_target]
      exact sq.w
    have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourceArrowTarget (Sp.{u}))
      (boundary (n + 1)).ι inferInstance
    let L := hBL.lift
    let R := hBR.lift
    have hLR : (L ≫ j) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
        (R ≫ j) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) :=
      hBL.fac_right.trans hBR.fac_right.symm
    let d := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_cospanFamilyOfArrows (L ≫ j) (R ≫ j) hLR
    have hd : (boundary (n + 1)).ι ≫ d = a ≫ ι ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary).app (Sp.{u}) := by
      apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_cospanFamily_hom_ext
      · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_cospanFamilyOfArrows_left]
        rw [← Category.assoc, hBL.fac_left, Category.assoc]
        rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramRightArrow, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι]
        simp only [Category.assoc, ← NatTrans.comp_app, ← pre_map, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_rightEdge]
        rfl
      · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_cospanFamilyOfArrows_right]
        rw [← Category.assoc, hBR.fac_left, Category.assoc]
        rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramTopArrow, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι]
        simp only [Category.assoc, ← NatTrans.comp_app, ← pre_map, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_topEdge]
        rfl
    let c := a ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramConeFamily (Sp.{u})
    have hcd : CommSq c (boundary (n + 1)).ι
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitConeProjection (horn 2 2 : SSet.{u + 1}) (Sp.{u})) d := by
      constructor
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramConeFamily_projection]
      exact hd.symm
    have : HasLiftingProperty (boundary (n + 1)).ι
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitConeProjection (horn 2 2 : SSet.{u + 1}) (Sp.{u})) :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeTerminalProjection_hasLiftingProperty_boundary
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction (horn 2 2 : SSet.{u + 1}) (Sp.{u})) n
    let U := hcd.lift
    let k := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeTerminalVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction (horn 2 2 : SSet.{u + 1}) (Sp.{u}))).ι
    let F := U ≫ k ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.inv).app (Sp.{u})
    have hFa : (boundary (n + 1)).ι ≫ F = a ≫ ι := by
      dsimp only [F]
      rw [← Category.assoc, ← Category.assoc, hcd.fac_left, Category.assoc]
      change a ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramConeFamily (Sp.{u}) ≫ k) ≫
        (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.inv).app (Sp.{u}) = _
      rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramConeFamily_ι]
      simp only [Category.assoc, ← NatTrans.comp_app, ← pre_map, Iso.inv_hom_id,
        pre_id, NatTrans.id_app, Category.comp_id]
      rfl
    have hv (v : (Δ[n + 1] : SSet.{u + 1}) _⦋0⦌) :
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex (F.app (Opposite.op ⦋0⦌) v) := by
      let w : (boundary (n + 1) : SSet.{u + 1}) _⦋0⦌ := ⟨v, by
        have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary.{u + 1} n (stdSimplex.obj₀Equiv.{u + 1} v)
        rw [Equiv.symm_apply_apply] at h
        exact h⟩
      have he := ConcreteCategory.congr_hom (NatTrans.congr_app hFa (Opposite.op ⦋0⦌)) w
      change F.app (Opposite.op ⦋0⦌) v = (a.app (Opposite.op ⦋0⦌) w).val at he
      rw [he]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (a.app (Opposite.op ⦋0⦌) w)
    let g := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex F hv
    have hg : g ≫ ι = F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _
    refine CommSq.HasLift.mk' { l := g, fac_left := ?_, fac_right := ?_ }
    · apply (cancel_mono ι).1
      rw [Category.assoc, hg, hFa]
    · change g ≫ ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = b
      rw [← Category.assoc, hg]
      have hFd : F ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary).app (Sp.{u}) = d := by
        dsimp only [F]
        simp only [Category.assoc, ← NatTrans.comp_app, ← pre_map]
        have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.inv =
            _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] (horn 2 2 : SSet.{u + 1}) := by
          simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary, Category.assoc, Iso.hom_inv_id, Category.comp_id]
        rw [hi]
        exact hcd.fac_right
      have hFL : F ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge).app (Sp.{u}) = L ≫ j := by
        have hh := congrArg (fun t ↦ t ≫ (pre horn₂₂.ι₀₂).app (Sp.{u})) hFd
        rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_cospanFamilyOfArrows_left] at hh
        simpa only [Category.assoc, ← NatTrans.comp_app, ← pre_map,
          _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_rightEdge] using hh
      have hh := congrArg
        (fun t ↦ t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) hFL
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt] at hh
      exact hh.trans hBL.fac_right

end SerrePositivity.KST.Spectra.OmegaSpectrum
