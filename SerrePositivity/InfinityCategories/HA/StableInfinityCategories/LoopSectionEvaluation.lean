module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopEvaluationLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceCalculus
/-!
概要：指定された実 loop 図式の切断から二つの評価の同値性を得る。
方針：相対境界を普遍 loop 錐へ持ち上げ、同じ切断の厳密な終点式を使う。
規約：安定性を仮定しない。使われ方：HA 1.4.2.27 の安定性判定の準備。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
lemma loopDiagramEvaluation_target_trivialKanFibration_of_section (X : SSet.{u})
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex X] (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X)
    (hs : s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 = 𝟙 X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro a b sq
  cases n with
  | zero =>
    let v := s.app (Opposite.op ⦋0⦌) (SSet.yonedaEquiv b)
    have hv : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1).app (Opposite.op ⦋0⦌) v =
        SSet.yonedaEquiv b :=
      ConcreteCategory.congr_hom (NatTrans.congr_app hs (Opposite.op ⦋0⦌))
        (SSet.yonedaEquiv b)
    refine CommSq.HasLift.mk' {
      l := SSet.yonedaEquiv.symm v
      fac_left := boundary.hom_ext₀
      fac_right := ?_ }
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, hv]
  | succ n =>
    let ι := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X)
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι
    let j := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (Δ[1] : SSet.{u})).obj X) _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroSourceArrow).ι
    have hBL : CommSq (a ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramRightArrow X) (boundary (n + 1)).ι
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourceArrowTarget X) b := by
      constructor
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramRightArrow_target]
      exact sq.w
    have hBR : CommSq (a ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramTopArrow X) (boundary (n + 1)).ι
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourceArrowTarget X) b := by
      constructor
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramTopArrow_target]
      exact sq.w
    have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourceArrowTarget X)
      (boundary (n + 1)).ι inferInstance
    let L := hBL.lift
    let R := hBR.lift
    have hLR : (L ≫ j) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
        (R ≫ j) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) :=
      hBL.fac_right.trans hBR.fac_right.symm
    let d := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_cospanFamilyOfArrows (L ≫ j) (R ≫ j) hLR
    have hd : (boundary (n + 1)).ι ≫ d = a ≫ ι ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary).app X := by
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
    let c := a ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramConeFamily X
    have hcd : CommSq c (boundary (n + 1)).ι
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitConeProjection (horn 2 2 : SSet.{u}) X) d := by
      constructor
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramConeFamily_projection]
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
      change a ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramConeFamily X ≫ k) ≫
        (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.inv).app X = _
      rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramConeFamily_ι]
      simp only [Category.assoc, ← NatTrans.comp_app, ← pre_map, Iso.inv_hom_id,
        pre_id, NatTrans.id_app, Category.comp_id]
      rfl
    have hv (v : (Δ[n + 1] : SSet.{u}) _⦋0⦌) :
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex (F.app (Opposite.op ⦋0⦌) v) := by
      let w : (boundary (n + 1) : SSet.{u}) _⦋0⦌ := ⟨v, by
        have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary.{u} n (stdSimplex.obj₀Equiv.{u} v)
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
      have hFd : F ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary).app X = d := by
        dsimp only [F]
        simp only [Category.assoc, ← NatTrans.comp_app, ← pre_map]
        have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.inv =
            _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] (horn 2 2 : SSet.{u}) := by
          simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary, Category.assoc, Iso.hom_inv_id, Category.comp_id]
        rw [hi]
        exact hcd.fac_right
      have hFL : F ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge).app X = L ≫ j := by
        have hh := congrArg (fun t ↦ t ≫ (pre horn₂₂.ι₀₂).app X) hFd
        rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_cospanFamilyOfArrows_left] at hh
        simpa only [Category.assoc, ← NatTrans.comp_app, ← pre_map,
          _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_rightEdge] using hh
      have hh := congrArg
        (fun t ↦ t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) hFL
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt] at hh
      exact hh.trans hBL.fac_right

lemma loopDiagramSection_isQCatEquivalence {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex X] (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X)
    (hs : s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 = 𝟙 X) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence s := by
  let := loopDiagramEvaluation_target_trivialKanFibration_of_section X s hs
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1)).isQCatEquivalence
  apply hp.cancel_right
  rw [hs]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.refl X).isQCatEquivalence
lemma loopDiagramEvaluation_source_isQCatEquivalence_of_loopEquivalence {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex X] (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X)
    (hs : s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0) :=
  (loopDiagramSection_isQCatEquivalence s hs).cancel_left hΩ
def loopDiagramFamilyIso_of_section {A X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex X] (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X)
    (hs : s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 = 𝟙 X)
    (f g : A ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X)
    (h : f ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 = g ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g := by
  let := loopDiagramEvaluation_target_trivialKanFibration_of_section X s hs
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorIsoOfTrivialKanFibration (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1) f g h
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
