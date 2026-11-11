module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.ArrowPrecompositionSquare
public import SerrePositivity.KST.LocalizingInvariants.IntervalPostcompositionFamily

/-!
概要：指定した始点の辺に沿う区間図式の前合成と、その元の合成二単体。
方針：終点の縦辺が恒等な合成正方形を curry し、最終時刻と両端点を回収する。
規約：同じ二単体を分母の二対三性へ渡せる。使われ方：span の pullback 輸送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

def intervalPrecompositionFamily {X : SSet.{u}} (T : (Δ[2] : SSet.{u}) ⟶ X) :
    (Δ[1] : SSet.{u}) ⟶ (ihom (Δ[1] : SSet.{u})).obj X :=
  curry (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPrecompositionFold ≫ T)

lemma intervalPrecompositionFamily_edge_zero {X : SSet.{u}} (T : (Δ[2] : SSet.{u}) ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge ((intervalPrecompositionFamily T).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) =
        SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫ T) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge ((curry (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPrecompositionFold ≫ T)).app
    (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_curry]
  have h : SSet.yonedaEquiv ((SSet.ι₀ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) ≫
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPrecompositionFold ≫ T) =
        SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫ T) := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPrecompositionFold_zero]
  exact h

lemma intervalPrecompositionFamily_edge_one {X : SSet.{u}} (T : (Δ[2] : SSet.{u}) ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge ((intervalPrecompositionFamily T).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) =
        SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ T) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge ((curry (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPrecompositionFold ≫ T)).app
    (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_curry]
  have h : SSet.yonedaEquiv ((SSet.ι₁ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) ≫
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPrecompositionFold ≫ T) =
        SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ T) := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPrecompositionFold_one]
  exact h

lemma exists_intervalPrecompositionFamily {X : SSet.{u}} [Quasicategory X]
    (f b : (Δ[1] : SSet.{u}) ⟶ X)
    (h : stdSimplex.δ (0 : Fin 2) ≫ b = stdSimplex.δ (1 : Fin 2) ≫ f) :
    ∃ T : (Δ[2] : SSet.{u}) ⟶ X,
      stdSimplex.δ (2 : Fin 3) ≫ T = b ∧ stdSimplex.δ (0 : Fin 3) ≫ T = f ∧
      stdSimplex.δ (0 : Fin 2) ≫ intervalPrecompositionFamily T = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) ∧
      intervalPrecompositionFamily T ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = b ∧
      intervalPrecompositionFamily T ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
          SSet.const (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
  have hb : X.δ 1 (SSet.yonedaEquiv f) = X.δ 0 (SSet.yonedaEquiv b) := by
    rw [intervalMap_source, intervalMap_target]
    have hh := congrArg (fun k : (Δ[0] : SSet.{u}) ⟶ X =>
      k.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) h
    exact hh.symm
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv b)
  let g : Truncated.Edge (X := (truncation 2).obj X) (X.δ 0 e.edge)
      (X.δ 0 (SSet.yonedaEquiv f)) := ⟨SSet.yonedaEquiv f, hb, rfl⟩
  obtain ⟨T, hT₂, hT₀, hTt⟩ := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.exists_arrowPrecompositionSquare e g
  have hT₂' : stdSimplex.δ (2 : Fin 3) ≫ T = b :=
    hT₂.trans (SSet.yonedaEquiv.symm_apply_apply b)
  have hT₀' : stdSimplex.δ (0 : Fin 3) ≫ T = f :=
    hT₀.trans (SSet.yonedaEquiv.symm_apply_apply f)
  refine ⟨T, hT₂', hT₀', ?_, ?_, ?_⟩
  · apply SSet.yonedaEquiv.injective
    change ((ihom (Δ[1] : SSet.{u})).obj X).δ 0
      (SSet.yonedaEquiv (curry (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPrecompositionFold ≫ T))) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) 0
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero, ← _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_uncurry_one, Equiv.symm_apply_apply,
      uncurry_curry, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPrecompositionFold_one, hT₀']
  · rw [intervalPrecompositionFamily, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval,
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowPrecompositionFold_source, hT₂']
  · rw [intervalPrecompositionFamily, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, hTt]
    exact congrArg SSet.const (intervalMap_target f)

end SerrePositivity.KST.LocalizingInvariants
