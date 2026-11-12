module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.ArrowPostcompositionSquare

/-!
概要：区間図式を指定した終点の辺に沿って、始点を固定した区間図式の辺へ拡張する。
方針：合成正方形を curry し、零時刻と両端点の評価を回収する。
規約：入力の区間と終点辺を厳密に保持。使われ方：span の第一脚固定の持ち上げ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma intervalMap_source {X : SSet.{u}} (f : (Δ[1] : SSet.{u}) ⟶ X) :
    X.δ 1 (SSet.yonedaEquiv f) =
      f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  calc
    X.δ 1 (SSet.yonedaEquiv f) = SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ f) :=
      SSet.yonedaEquiv_naturality (SimplexCategory.δ (1 : Fin 2)) f
    _ = f.app (Opposite.op ⦋0⦌) (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2))) :=
      SSet.yonedaEquiv_comp _ _
    _ = _ := congrArg (f.app (Opposite.op ⦋0⦌)) (by decide)

lemma intervalMap_target {X : SSet.{u}} (f : (Δ[1] : SSet.{u}) ⟶ X) :
    X.δ 0 (SSet.yonedaEquiv f) =
      f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
  calc
    X.δ 0 (SSet.yonedaEquiv f) = SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ f) :=
      SSet.yonedaEquiv_naturality (SimplexCategory.δ (0 : Fin 2)) f
    _ = f.app (Opposite.op ⦋0⦌) (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2))) :=
      SSet.yonedaEquiv_comp _ _
    _ = _ := congrArg (f.app (Opposite.op ⦋0⦌)) (by decide)

lemma exists_intervalPostcompositionFamily {X : SSet.{u}} [Quasicategory X]
    (f b : (Δ[1] : SSet.{u}) ⟶ X)
    (h : stdSimplex.δ (1 : Fin 2) ≫ b = stdSimplex.δ (0 : Fin 2) ≫ f) :
    ∃ R : (Δ[1] : SSet.{u}) ⟶ (ihom (Δ[1] : SSet.{u})).obj X,
      stdSimplex.δ (1 : Fin 2) ≫ R = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) ∧
      R ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
        SSet.const (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ∧
      R ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = b := by
  have hb : X.δ 1 (SSet.yonedaEquiv b) = X.δ 0 (SSet.yonedaEquiv f) := by
    rw [intervalMap_source, intervalMap_target]
    have hh := congrArg (fun k : (Δ[0] : SSet.{u}) ⟶ X =>
      k.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) h
    exact hh
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv f)
  let g : Truncated.Edge (X := (truncation 2).obj X) (X.δ 0 e.edge)
      (X.δ 0 (SSet.yonedaEquiv b)) :=
    { edge := SSet.yonedaEquiv b
      src_eq := hb
      tgt_eq := rfl }
  obtain ⟨H, hH₀, hHs, hHt⟩ := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.exists_arrowPostcompositionSquare e g
  have hH₀' : SSet.ι₀ ≫ H = f := by
    exact hH₀.trans (SSet.yonedaEquiv.symm_apply_apply f)
  have hHt' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[1] ≫ H = b := by
    exact hHt.trans (SSet.yonedaEquiv.symm_apply_apply b)
  refine ⟨curry H, ?_, ?_, ?_⟩
  · apply SSet.yonedaEquiv.injective
    change ((ihom (Δ[1] : SSet.{u})).obj X).δ 1 (SSet.yonedaEquiv (curry H)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) 0
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero, ← _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_uncurry_zero, Equiv.symm_apply_apply,
      uncurry_curry, hH₀']
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, hHs]
    apply congrArg SSet.const
    change X.δ 1 (SSet.yonedaEquiv f) =
      f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
    exact intervalMap_source f
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, hHt']

end SerrePositivity.KST.LocalizingInvariants
