module
public import SerrePositivity.InfinityCategories.Stable.TerminalSpanRelative
public import SerrePositivity.InfinityCategories.Stable.TerminalMappingSpace
public import SerrePositivity.InfinityCategories.Core.HomotopyEvaluationClass
public import SerrePositivity.InfinityCategories.Stable.SuspensionSpanComparison

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
namespace SerrePositivity.InfinityCategories

/-- 概要：終対象を両端とする span への Hom は始点の Hom と全単射で対応する。
方針：相対終点境界充填による Hom の全単射を始点評価へ適用する。
規約：X は quasicategory。使われ方：span の比較の始点による判定。 -/
lemma spanSourceEvaluation_homMap_bijective {X : SSet.{u}} [Quasicategory X]
    (f g : (horn 2 0 : SSet.{u}) ⟶ X)
    (hg₁ : IsTerminalVertex ((horn₂₀.ι₀₁ ≫ g).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2))))
    (hg₂ : IsTerminalVertex ((horn₂₀.ι₀₂ ≫ g).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) : Function.Bijective
      ((hoFunctor.map (spanSourceEvaluation X)).toFunctor.map :
        (SSet.HomotopyCategory.mk (functorVertex f) ⟶
          SSet.HomotopyCategory.mk (functorVertex g)) → _) :=
  homotopyCategoryMap_bijective_of_terminalBoundaryLifting (spanSourceEvaluation X)
    (terminalBoundaryLifting_spanSource_of_terminalTargets g hg₁ hg₂) (functorVertex f)

/-- 概要：suspension の span への二つの h の射は始点成分が一致すれば等しい。
方針：suspension の零角を二つの終対象として使い、Hom の単射性を適用する。
規約：指定した suspension 四角形を用い、元の四角形に普遍性は不要。
使われ方：接続射のための span の比較の選択独立性。 -/
lemma suspensionSpan_hom_ext {X : SSet.{u}} [Quasicategory X]
    (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (s : SuspensionSquare (squareVertex F 0 0))
    {a b : (SSet.HomotopyCategory.mk (functorVertex (pushoutSpan F)) :
      hoFunctor.obj ((ihom (horn 2 0 : SSet.{u})).obj X)) ⟶
        SSet.HomotopyCategory.mk (functorVertex (pushoutSpan s.square))}
    (h : (hoFunctor.map (spanSourceEvaluation X)).toFunctor.map a =
      (hoFunctor.map (spanSourceEvaluation X)).toFunctor.map b) : a = b := by
  have hg₁ : IsTerminalVertex ((horn₂₀.ι₀₁ ≫ pushoutSpan s.square).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
    rw [pushoutSpan, ← Category.assoc, spanSquareBoundary_bottomEdge]
    exact s.other_zero.2
  have hg₂ : IsTerminalVertex ((horn₂₀.ι₀₂ ≫ pushoutSpan s.square).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
    rw [pushoutSpan, ← Category.assoc, spanSquareBoundary_leftEdge]
    exact s.zero_corner.2
  exact (spanSourceEvaluation_homMap_bijective (pushoutSpan F)
    (pushoutSpan s.square) hg₁ hg₂).1 h

/-- 概要：span の始点評価は零頂点の包含の Yoneda 表示での評価である。
方針：前合成と評価の式と、第一辺の零端点を比較する。
規約：単体集合の射の厳密な等式。使われ方：始点固定条件を評価した類へ移す。 -/
lemma spanSourceEvaluation_eq_evaluate (X : SSet.{u}) :
    spanSourceEvaluation X = evaluateFunctorAt (Y := X)
      (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ horn₂₀.ι₀₁)) := by
  unfold spanSourceEvaluation
  rw [stable_pre_evaluateFunctorAt]
  congr 1
  rw [SSet.yonedaEquiv_comp]
  exact congrArg (horn₂₀.ι₀₁.app (Opposite.op ⦋0⦌)) (by decide)

/-- 概要：始点を固定した suspension span への比較は h で同じ射を与える。
方針：固定した始点で評価した二つの類を同じ恒等成分と比較し、始点評価の単射性で戻す。
規約：指定 suspension の span への実際のホモトピーの選択は自由。
使われ方：接続射の入力である span 比較の選択独立性。 -/
lemma suspensionSpanHomotopy_homMk_eq {X : SSet.{u}} [Quasicategory X]
    (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (s : SuspensionSquare (squareVertex F 0 0))
    (H J : SSet.Homotopy (pushoutSpan F) (pushoutSpan s.square))
    (hH : ((stdSimplex.δ (1 : Fin 2) ≫ horn₂₀.ι₀₁) ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      CartesianMonoidalCategory.snd Δ[0] Δ[1] ≫ SSet.const (squareVertex F 0 0))
    (hJ : ((stdSimplex.δ (1 : Fin 2) ≫ horn₂₀.ι₀₁) ▷ (Δ[1] : SSet.{u})) ≫ J.h =
      CartesianMonoidalCategory.snd Δ[0] Δ[1] ≫ SSet.const (squareVertex F 0 0)) :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy J) := by
  apply suspensionSpan_hom_ext F s
  rw [spanSourceEvaluation_eq_evaluate]
  exact homotopyEvaluation_eq_of_fixedVertex H J _ _ hH hJ

end SerrePositivity.InfinityCategories
