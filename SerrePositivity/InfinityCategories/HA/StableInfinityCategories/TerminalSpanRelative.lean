module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.TerminalArrowRelative
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SpanFamilies
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.SuspensionDiagramArrows

/-! # 終対象を両端とする span の相対境界充填

概要：両端が終対象である span は、共通の始点の評価に関する相対終点境界を充填する。
方針：二辺を同じ始点の族の上で延長し、ホーンの pushout で貼り合わせる。
規約：他の境界の span の両端には条件を課さない。
使われ方：S4 の suspension の span への比較の一意性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：標準 span の図式の共通の始点を評価する。
方針：第一辺で制限して区間の零端点を評価する。
規約：Λ[2,0] の零頂点。使われ方：span 比較の始点の固定。 -/
def spanSourceEvaluation (X : SSet.{u}) : (ihom (horn 2 0 : SSet.{u})).obj X ⟶ X :=
  (pre horn₂₀.ι₀₁).app X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))

/-- 概要：標準 span の第二辺の始点評価も共通の始点評価に一致する。
方針：前合成と頂点評価の可換性を使い、二辺の始点を比較する。
規約：単体集合の射としての厳密な等式。使われ方：二辺の相対延長の整合。 -/
lemma spanSourceEvaluation_right (X : SSet.{u}) :
    (pre horn₂₀.ι₀₂).app X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      spanSourceEvaluation X := by
  unfold spanSourceEvaluation
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt]
  congr 1

/-- 概要：両端が終対象である span は共通始点評価の相対終点境界を充填する。
方針：二辺の相対境界充填を同じ始点の上で行い、span の族として貼る。
規約：値域に quasicategory 性を仮定しない。
使われ方：指定した始点の比較の上での suspension span の一意性。 -/
lemma terminalBoundaryLifting_spanSource_of_terminalTargets {X : SSet.{u}}
    (g : (horn 2 0 : SSet.{u}) ⟶ X)
    (hg₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex ((horn₂₀.ι₀₁ ≫ g).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2))))
    (hg₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex ((horn₂₀.ι₀₂ ≫ g).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting (spanSourceEvaluation X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g) := by
  intro n a b hb sq
  let L₀ := a ≫ (pre horn₂₀.ι₀₁).app X
  let R₀ := a ≫ (pre horn₂₀.ι₀₂).app X
  have hL₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ L₀ =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (horn₂₀.ι₀₁ ≫ g)) := by
    dsimp only [L₀]
    rw [← Category.assoc, hb, SSet.yonedaEquiv_symm_comp]
    rfl
  have hR₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ R₀ =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (horn₂₀.ι₀₂ ≫ g)) := by
    dsimp only [R₀]
    rw [← Category.assoc, hb, SSet.yonedaEquiv_symm_comp]
    rfl
  have sqL : CommSq L₀ (boundary (n + 1)).ι
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) b := by
    constructor
    simpa only [L₀, Category.assoc, spanSourceEvaluation] using sq.w
  have sqR : CommSq R₀ (boundary (n + 1)).ι
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) b := by
    constructor
    dsimp only [R₀]
    rw [Category.assoc, spanSourceEvaluation_right]
    exact sq.w
  obtain ⟨L, hL, hLp⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.terminalBoundaryLifting_arrowSource_of_terminalTarget
    (horn₂₀.ι₀₁ ≫ g) hg₁ n L₀ b hL₀ sqL
  obtain ⟨R, hR, hRp⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.terminalBoundaryLifting_arrowSource_of_terminalTarget
    (horn₂₀.ι₀₂ ≫ g) hg₂ n R₀ b hR₀ sqR
  let d := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_spanFamilyOfArrows L R (hLp.trans hRp.symm)
  refine ⟨d, ?_, ?_⟩
  · apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_spanFamily_hom_ext
    · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_spanFamilyOfArrows_left, hL]
    · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_spanFamilyOfArrows_right, hR]
  · change d ≫ ((pre horn₂₀.ι₀₁).app X ≫ _) = b
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_spanFamilyOfArrows_left, hLp]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
