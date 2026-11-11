module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionDiagrams
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SpanFamilies
public import SerrePositivity.KST.SConstruction.CofiberCompletion

/-! # cofiber の選択の自明 Kan ファイブレーション
概要：cofiber 四角形の入力への射影は全境界を持ち上げる。
方針：零対象への左辺を補完して span を作り、普遍的な押し出しを補完する。
規約：α-S の IsStable の存在条件を零次元で用いる。
使われ方：gapped 図式と McCarthy 加法性の関手的な cofiber。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：cofiber 四角形の入力への射影は trivial Kan fibration。
方針：零次元は安定性による cofiber の存在、正次元は零対象への辺と押し出しの相対補完。
規約：安定な quasicategory を仮定する。使われ方：cofiber を族として関手的に選ぶ。 -/
instance cofiberProjection_trivialKanFibration (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (cofiberProjection C) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro a b sq
  let ι : cofiberDiagrams C ⟶ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι
  cases n with
  | zero =>
    let f := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[1] : SSet.{u}) C).symm (SSet.yonedaEquiv b)
    let t := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenCofiberSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv f))
    have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ t.square = f := by
      rw [t.bottom_edge]
      exact SSet.yonedaEquiv.symm_apply_apply f
    let v : (cofiberDiagrams C) _⦋0⦌ := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex t.square, by
      intro α
      have hα : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
      rw [hα, op_id, CategoryTheory.Functor.map_id_apply]
      constructor
      · rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagram_functorVertex]
        exact t.zero_corner
      · change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C t.square))
        rw [Equiv.symm_apply_apply]
        exact t.isPushout⟩
    refine CommSq.HasLift.mk' {
      l := SSet.yonedaEquiv.symm v
      fac_left := boundary.hom_ext₀
      fac_right := ?_ }
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ t.square) = SSet.yonedaEquiv b
    rw [ht]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C).apply_symm_apply _
  | succ n =>
    let j := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (Δ[1] : SSet.{u})).obj C) _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroTargetArrow).ι
    have sqL : CommSq (a ≫ cofiberZeroArrow C) (boundary (n + 1)).ι
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.zeroTargetArrowSource C)
        (b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) := by
      constructor
      rw [Category.assoc, cofiberZeroArrow_source, ← Category.assoc, sq.w, Category.assoc]
    have : HasLiftingProperty (boundary (n + 1)).ι (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.zeroTargetArrowSource C) :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem _ inferInstance
    let L := sqL.lift
    have hL : b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
        (L ≫ j) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := sqL.fac_right.symm
    let d := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_spanFamilyOfArrows b (L ≫ j) hL
    have hd : (boundary (n + 1)).ι ≫ d = a ≫ ι ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary).app C := by
      apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_spanFamily_hom_ext
      · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_spanFamilyOfArrows_left]
        rw [← sq.w]
        simp only [cofiberProjection, Category.assoc, ← NatTrans.comp_app, ← pre_map,
          _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_bottomEdge]
        rfl
      · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_spanFamilyOfArrows_right]
        rw [← Category.assoc, sqL.fac_left, Category.assoc, cofiberZeroArrow_ι]
        simp only [Category.assoc, ← NatTrans.comp_app, ← pre_map, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_leftEdge]
        rfl
    have sqP : CommSq (a ≫ cofiberForgetZero C) (boundary (n + 1)).ι (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pushoutProjection C) d := by
      constructor
      change (a ≫ cofiberForgetZero C ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsPushoutDiagramVertex).ι) ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary).app C = _
      rw [Category.assoc, cofiberForgetZero_ι]
      exact hd.symm
    have : HasLiftingProperty (boundary (n + 1)).ι (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pushoutProjection C) :=
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pushoutProjection_hasLiftingProperty_boundary C n
    let U := sqP.lift
    let F := U ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsPushoutDiagramVertex).ι
    have hc : (boundary (n + 1)).ι ≫ F = a ≫ ι := by
      rw [← Category.assoc, sqP.fac_left, Category.assoc, cofiberForgetZero_ι]
    have hv (v : (Δ[n + 1] : SSet.{u}) _⦋0⦌) :
        IsCofiberDiagramVertex (F.app (Opposite.op ⦋0⦌) v) := by
      let w : (boundary (n + 1) : SSet.{u}) _⦋0⦌ := ⟨v, by
        have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary.{u} n (stdSimplex.obj₀Equiv.{u} v)
        rw [Equiv.symm_apply_apply] at h
        exact h⟩
      have hh := ConcreteCategory.congr_hom (NatTrans.congr_app hc (Opposite.op ⦋0⦌)) w
      change F.app (Opposite.op ⦋0⦌) v = (a.app (Opposite.op ⦋0⦌) w).val at hh
      rw [hh]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (a.app (Opposite.op ⦋0⦌) w)
    let g := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift IsCofiberDiagramVertex F hv
    have hg : g ≫ ι = F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _
    refine CommSq.HasLift.mk' { l := g, fac_left := ?_, fac_right := ?_ }
    · apply (cancel_mono ι).1
      rw [Category.assoc, hg, hc]
    · change g ≫ ι ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge).app C = b
      rw [← Category.assoc, hg]
      change (U ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsPushoutDiagramVertex).ι) ≫
        (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge).app C = b
      rw [Category.assoc, ← pushoutProjection_bottom, ← Category.assoc, sqP.fac_right,
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_spanFamilyOfArrows_left]

end SerrePositivity.KST.SConstruction
