module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.TerminalSpanRelative
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.TerminalMappingSpace
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HomotopyEvaluationClass
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSpanComparison

/-! # 終対象へ向かう span 比較の一意性

概要：終対象を両端とする span への h の射は、共通始点での成分だけで決まる。
方針：相対終点境界充填から指定終点への写像空間の trivial Kan fibration を得る。
規約：元の span の両端には終対象性を課さない。
使われ方：S4 の cofiber の接続射の選択独立性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：終対象を両端とする span への Hom は始点の Hom と全単射で対応する。
方針：相対終点境界充填による Hom の全単射を始点評価へ適用する。
規約：X は quasicategory。使われ方：span の比較の始点による判定。 -/
lemma spanSourceEvaluation_homMap_bijective {X : SSet.{u}} [Quasicategory X]
    (f g : (horn 2 0 : SSet.{u}) ⟶ X)
    (hg₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex ((horn₂₀.ι₀₁ ≫ g).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2))))
    (hg₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex ((horn₂₀.ι₀₂ ≫ g).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) : Function.Bijective
      ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.spanSourceEvaluation X)).toFunctor.map :
        (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) ⟶
          SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g)) → _) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.homotopyCategoryMap_bijective_of_terminalBoundaryLifting (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.spanSourceEvaluation X)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.terminalBoundaryLifting_spanSource_of_terminalTargets g hg₁ hg₂) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)

/-- 概要：suspension の span への二つの h の射は始点成分が一致すれば等しい。
方針：suspension の零角を二つの終対象として使い、Hom の単射性を適用する。
規約：指定した suspension 四角形を用い、元の四角形に普遍性は不要。
使われ方：接続射のための span の比較の選択独立性。 -/
lemma suspensionSpan_hom_ext {X : SSet.{u}} [Quasicategory X]
    (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 0 0))
    {a b : (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan F)) :
      hoFunctor.obj ((ihom (horn 2 0 : SSet.{u})).obj X)) ⟶
        SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan s.square))}
    (h : (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.spanSourceEvaluation X)).toFunctor.map a =
      (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.spanSourceEvaluation X)).toFunctor.map b) : a = b := by
  have hg₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex ((horn₂₀.ι₀₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan s.square).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_bottomEdge]
    exact s.other_zero.2
  have hg₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex ((horn₂₀.ι₀₂ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan s.square).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_leftEdge]
    exact s.zero_corner.2
  exact (spanSourceEvaluation_homMap_bijective (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan s.square) hg₁ hg₂).1 h

/-- 概要：span の始点評価は零頂点の包含の Yoneda 表示での評価である。
方針：前合成と評価の式と、第一辺の零端点を比較する。
規約：単体集合の射の厳密な等式。使われ方：始点固定条件を評価した類へ移す。 -/
lemma spanSourceEvaluation_eq_evaluate (X : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.spanSourceEvaluation X = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X)
      (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ horn₂₀.ι₀₁)) := by
  unfold _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.spanSourceEvaluation
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt]
  congr 1
  rw [SSet.yonedaEquiv_comp]
  exact congrArg (horn₂₀.ι₀₁.app (Opposite.op ⦋0⦌)) (by decide)

/-- 概要：始点を固定した suspension span への比較は h で同じ射を与える。
方針：固定した始点で評価した二つの類を同じ恒等成分と比較し、始点評価の単射性で戻す。
規約：指定 suspension の span への実際のホモトピーの選択は自由。
使われ方：接続射の入力である span 比較の選択独立性。 -/
lemma suspensionSpanHomotopy_homMk_eq {X : SSet.{u}} [Quasicategory X]
    (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 0 0))
    (H J : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan F) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan s.square))
    (hH : ((stdSimplex.δ (1 : Fin 2) ≫ horn₂₀.ι₀₁) ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      CartesianMonoidalCategory.snd Δ[0] Δ[1] ≫ SSet.const (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 0 0))
    (hJ : ((stdSimplex.δ (1 : Fin 2) ≫ horn₂₀.ι₀₁) ▷ (Δ[1] : SSet.{u})) ≫ J.h =
      CartesianMonoidalCategory.snd Δ[0] Δ[1] ≫ SSet.const (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 0 0)) :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy J) := by
  apply suspensionSpan_hom_ext F s
  rw [spanSourceEvaluation_eq_evaluate]
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyEvaluation_eq_of_fixedVertex H J _ _ hH hJ

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
