module
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.Pullback
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.SimplexVertexDetection
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.StdSimplexProductMap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalMappingSpace
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalUniqueness
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiniteShapes
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PushoutShape

/-! # 終対象への辺との始点を固定した比較

概要：同じ始点を持つ任意の辺から、終対象への辺への単体的ホモトピーを構成する。
方針：終対象での射の一意性を合成三角形に直し、左辺を潰した正方形で引き戻す。
規約：始点はホモトピーの全体で厳密に固定する。
使われ方：cofiber の span から suspension の span への比較。

対応節は Kerodon 7.1（Tag 02H1）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：正方形の左辺を潰す標準二単体への射。
方針：横座標零を零、それ以外を縦座標に一を加えた頂点に写す。
規約：左下・左上が零、右下が一、右上が二。
使われ方：合成三角形から始点固定の正方形を作る。 -/
def stableTriangleComparisonShape : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[2] :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexProductMap {
    toFun p := if p.1 = 0 then 0 else p.2.succ
    monotone' := by decide }

/-- 概要：比較形状の下辺は二単体の第一辺。
方針：二頂点で計算する。規約：面番号二。
使われ方：ホモトピーの始点の回収。 -/
lemma stableTriangleComparisonShape_bottom :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ stableTriangleComparisonShape.{u} = stdSimplex.δ (2 : Fin 3) := by
  apply SSet.yonedaEquiv.injective
  apply stdSimplex.ext
  intro i
  fin_cases i <;> rfl

/-- 概要：比較形状の上辺は二単体の対角の辺。
方針：二頂点で計算する。規約：面番号一。
使われ方：ホモトピーの終点の回収。 -/
lemma stableTriangleComparisonShape_top :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ stableTriangleComparisonShape.{u} = stdSimplex.δ (1 : Fin 3) := by
  apply SSet.yonedaEquiv.injective
  apply stdSimplex.ext
  intro i
  fin_cases i <;> rfl

/-- 概要：比較形状の左辺は零頂点で定値。
方針：二頂点で計算する。
規約：単体集合の射としての等式。使われ方：始点の固定。 -/
lemma stableTriangleComparisonShape_source :
    (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ stableTriangleComparisonShape =
      snd Δ[0] Δ[1] ≫ SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 3)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_vertices
  apply ConcreteCategory.hom_ext
  rintro ⟨p, q⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective p
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective q
  fin_cases i; fin_cases j <;> decide

/-- 概要：同じ始点の任意の辺から終対象への辺へ、始点固定のホモトピーがある。
方針：終対象での射の一意性を合成三角形で実現し、比較形状で引き戻す。
規約：終点への辺は指定されたものを厳密に保持する。
使われ方：suspension の span への図式間の辺の構成。 -/
lemma exists_terminalArrowComparison {X : SSet.{u}} [Quasicategory X]
    {x y z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (g : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex z) :
    ∃ H : SSet.Homotopy (SSet.yonedaEquiv.symm f.edge) (SSet.yonedaEquiv.symm g.edge),
      (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ H.h =
        snd Δ[0] Δ[1] ≫ SSet.const x := by
  let k := Classical.choice (hz.nonempty_edge y)
  have h := hz.isTerminalHo.hom_ext
    (SSet.Truncated.HomotopyCategory.homMk f ≫ SSet.Truncated.HomotopyCategory.homMk k)
    (SSet.Truncated.HomotopyCategory.homMk g)
  obtain ⟨t⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac h
  let T : (Δ[2] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm t.simplex
  have hb : stdSimplex.δ (2 : Fin 3) ≫ T = SSet.yonedaEquiv.symm f.edge := by
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp]
    exact (congrArg (fun v ↦ X.δ 2 v) (SSet.yonedaEquiv.apply_symm_apply t.simplex)).trans
      (t.d₂.trans (SSet.yonedaEquiv.apply_symm_apply f.edge).symm)
  have ht : stdSimplex.δ (1 : Fin 3) ≫ T = SSet.yonedaEquiv.symm g.edge := by
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp]
    exact (congrArg (fun v ↦ X.δ 1 v) (SSet.yonedaEquiv.apply_symm_apply t.simplex)).trans
      (t.d₁.trans (SSet.yonedaEquiv.apply_symm_apply g.edge).symm)
  have hv : T.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 3)) = x := by
    have h₀ : (stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3)) ≫ T =
        SSet.yonedaEquiv.symm x := by
      rw [Category.assoc, hb]
      exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSimplex_source f
    have hh := congrArg SSet.yonedaEquiv h₀
    have hv₀ : SSet.yonedaEquiv
        (stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) :
          (Δ[0] : SSet.{u}) ⟶ Δ[2]) = stdSimplex.obj₀Equiv.symm (0 : Fin 3) := by decide
    simpa only [SSet.yonedaEquiv_comp, hv₀, Equiv.apply_symm_apply] using hh
  let H : SSet.Homotopy (SSet.yonedaEquiv.symm f.edge) (SSet.yonedaEquiv.symm g.edge) := {
    h := stableTriangleComparisonShape ≫ T
    h₀ := by
      change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ (stableTriangleComparisonShape ≫ T) = _
      rw [← Category.assoc, stableTriangleComparisonShape_bottom, hb]
      rfl
    h₁ := by
      change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ (stableTriangleComparisonShape ≫ T) = _
      rw [← Category.assoc, stableTriangleComparisonShape_top, ht]
      rfl
    rel := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro s
      exact False.elim s.1.property }
  refine ⟨H, ?_⟩
  change (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫
    (stableTriangleComparisonShape ≫ T) = _
  rw [← Category.assoc, stableTriangleComparisonShape_source, Category.assoc,
    SSet.const_comp, hv]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
