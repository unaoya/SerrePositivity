module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PushoutComparisonInvertible
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.SuspensionDiagramArrows

/-!
概要：押し出し四角形の比較の可逆性を入力 span の三つの角で検査する。
方針：span の全頂点を標準辺の端点として読み、既存の普遍余錐の反映を使う。
規約：一般安定性は仮定しない。
使われ方：回転した cofiber の最初の二成分からの比較の可逆性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：入力 span の頂点は元の四角形の三つの角のいずれかである。
方針：標準二単体の三頂点を二つの辺の端点として列挙する。
規約：余錐頂点は含めない。使われ方：比較の全頂点での可逆性。 -/
lemma spanSquareBoundary_vertex_cases (v : (horn 2 0 : SSet.{u}) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary.app (Opposite.op ⦋0⦌) v =
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (𝟙 (Δ[1] ⊗ Δ[1] : SSet.{u})) 0 0 ∨
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary.app (Opposite.op ⦋0⦌) v =
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (𝟙 (Δ[1] ⊗ Δ[1] : SSet.{u})) 1 0 ∨
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary.app (Opposite.op ⦋0⦌) v =
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (𝟙 (Δ[1] ⊗ Δ[1] : SSet.{u})) 0 1 := by
  rcases v with ⟨v, hv⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective v
  fin_cases i
  · left
    have he : (⟨stdSimplex.obj₀Equiv.symm (0 : Fin 3), hv⟩ :
        (horn 2 0 : SSet.{u}) _⦋0⦌) = horn₂₀.ι₀₁.app (Opposite.op ⦋0⦌)
          (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
      apply Subtype.ext
      apply stdSimplex.ext
      intro a
      fin_cases a
      rfl
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary.app (Opposite.op ⦋0⦌)
      (⟨stdSimplex.obj₀Equiv.symm (0 : Fin 3), hv⟩ : (horn 2 0 : SSet.{u}) _⦋0⦌) = _
    rw [he] -- normalized vertex
    change (horn₂₀.ι₀₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary).app (Opposite.op ⦋0⦌) _ = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_bottomEdge]
    rfl
  · right; left
    have he : (⟨stdSimplex.obj₀Equiv.symm (1 : Fin 3), hv⟩ :
        (horn 2 0 : SSet.{u}) _⦋0⦌) = horn₂₀.ι₀₁.app (Opposite.op ⦋0⦌)
          (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
      apply Subtype.ext
      apply stdSimplex.ext
      intro a
      fin_cases a
      rfl
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary.app (Opposite.op ⦋0⦌)
      (⟨stdSimplex.obj₀Equiv.symm (1 : Fin 3), hv⟩ : (horn 2 0 : SSet.{u}) _⦋0⦌) = _
    rw [he] -- normalized vertex
    change (horn₂₀.ι₀₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary).app (Opposite.op ⦋0⦌) _ = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_bottomEdge]
    rfl
  · right; right
    have he : (⟨stdSimplex.obj₀Equiv.symm (2 : Fin 3), hv⟩ :
        (horn 2 0 : SSet.{u}) _⦋0⦌) = horn₂₀.ι₀₂.app (Opposite.op ⦋0⦌)
          (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
      apply Subtype.ext
      apply stdSimplex.ext
      intro a
      fin_cases a
      rfl
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary.app (Opposite.op ⦋0⦌)
      (⟨stdSimplex.obj₀Equiv.symm (2 : Fin 3), hv⟩ : (horn 2 0 : SSet.{u}) _⦋0⦌) = _
    rw [he] -- normalized vertex
    change (horn₂₀.ι₀₂ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary).app (Opposite.op ⦋0⦌) _ = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_leftEdge]
    rfl

/-- 概要：押し出し間の比較辺は入力 span の三角で可逆なら可逆である。
方針：全評価による可逆性判定と普遍余錐の可逆性反映を接続する。
規約：元の比較辺を選び直さない。
使われ方：cofiber 図式の回転後の比較の検出。 -/
lemma pushoutComparison_isInvertible_of_three_corners {X : SSet.{u}} [Quasicategory X]
    {F G : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare F)
    (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare G)
    (e : Truncated.Edge (X := (truncation 2).obj
      ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G))
    (h : ∀ i j : Fin 2, (i = 0 ∨ j = 0) → _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (e.map ((truncation 2).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (𝟙 (Δ[1] ⊗ Δ[1] : SSet.{u})) i j))))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e := by
  let a : Truncated.Edge (X := (truncation 2).obj ((ihom (horn 2 0 : SSet.{u})).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan G)) :=
    e.map ((truncation 2).map ((pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary).app X))
  have ha : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge a := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isInvertibleEdge_iff_evaluateFunctorAt a).mpr
    intro v
    have he : (a.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) v))).edge =
        (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary.app (Opposite.op ⦋0⦌) v)))).edge :=
      congrArg (fun f ↦ f.app (Opposite.op ⦋1⦌) e.edge)
        (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary v)
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mpr
    rcases spanSquareBoundary_vertex_cases v with hv | hv | hv
    · rw [hv]; exact h 0 0 (Or.inl rfl)
    · rw [hv]; exact h 1 0 (Or.inr rfl)
    · rw [hv]; exact h 0 1 (Or.inl rfl)
  let H := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge e
  have hspan : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableHomotopyPrecomp _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary H)) := by
    have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableHomotopyPrecomp _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary H)).edge = a.edge := by
      change SSet.yonedaEquiv (curry ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary ▷ (Δ[1] : SSet.{u})) ≫
        uncurry (SSet.yonedaEquiv.symm e.edge))) = _
      rw [← uncurry_pre_app, curry_uncurry, SSet.yonedaEquiv_comp,
        Equiv.apply_symm_apply]
      rfl
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mpr ha
  have hi := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pushoutSquareHomotopy_isInvertible_of_span F G hF hG H hspan
  have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H).edge = e.edge := by
    change SSet.yonedaEquiv (curry (uncurry (SSet.yonedaEquiv.symm e.edge))) = _
    rw [curry_uncurry, Equiv.apply_symm_apply]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mp hi

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
