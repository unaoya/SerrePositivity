module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FiniteSpanNerveIso
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.NerveFinalInitialComma
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalCoconeRestriction
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.EdgeTargetCocone
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalOpposite
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.TerminalPointAnodyne
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.StdSimplexTerminal
public import Mathlib.CategoryTheory.Category.GaloisConnection
public import Mathlib.CategoryTheory.Adjunction.Comma

/-!
概要：恒等な第一枝を持つ標準 span を、第二枝の一本の辺へ共終的に畳む。
方針：三点半順序と二点鎖の Galois 接続から、各右 comma の実始対象を構成する。
規約：通常の Final だけで済ませず、元の nerve の right cofinal 性を証明する。
使われ方：辺の pushout を射圏の span 余極限として扱う際の始点側の計算。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 二点鎖を標準 span の始点と第二枝の終点へ含める。 -/
def spanRightSection (b : ULift.{u} (Fin 2)) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FiniteSpanIndex.{u} :=
  ⟨if b.down = 0 then .zero else .right⟩

/-- 標準 span の第一枝を零時刻へ畳み、第二枝を二点鎖として読む。 -/
def spanRightProjection (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FiniteSpanIndex.{u}) : ULift.{u} (Fin 2) :=
  ⟨if x.down = .right then 1 else 0⟩

/-- この畳み込みは、第二枝の包含の右随伴。 -/
lemma spanRight_galoisConnection : GaloisConnection spanRightSection.{u} spanRightProjection := by
  rintro ⟨b⟩ ⟨x⟩
  change ((if b = 0 then _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FiniteSpanVertex.zero else .right) = .zero ∨
    (if b = 0 then _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FiniteSpanVertex.zero else .right) = x) ↔
      b ≤ if x = .right then 1 else 0
  fin_cases b <;> cases x <;> decide

/-- 元の三点 span から元の二点鎖への通常の関手。 -/
def spanRightProjectionFunctor : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FiniteSpanIndex.{u} ⥤ ULift.{u} (Fin 2) :=
  spanRight_galoisConnection.monotone_u.functor

/-- 各右 comma の始対象から得る、同じ nerve 写像の right cofinal 性。 -/
lemma spanRightProjectionFunctor_isRightCofinal :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (nerveMap spanRightProjectionFunctor.{u}) := by
  let adj := spanRight_galoisConnection.{u}.adjunction
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.nerveMap_isRightCofinal_of_initial_comma spanRightProjectionFunctor
  intro b
  exact ⟨StructuredArrow.mk (adj.unit.app b),
    ⟨mkInitialOfLeftAdjoint spanRightProjectionFunctor adj b⟩⟩

/-- 元の標準 span ホーンから標準区間への実畳み込み。 -/
def spanRightCollapse : (horn 2 0 : SSet.{u}) ⟶ Δ[1] :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.finiteSpanNerveIso.inv ≫ nerveMap spanRightProjectionFunctor ≫ (stdSimplex.isoNerve 1).inv

/-- 元の標準ホーンの実畳み込みは right cofinal。 -/
lemma spanRightCollapse_isRightCofinal : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal spanRightCollapse.{u} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_isIso _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.finiteSpanNerveIso.inv).comp
    (spanRightProjectionFunctor_isRightCofinal.comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_isIso (stdSimplex.isoNerve 1).inv))

/-- 第一枝は零頂点への定値射になる。 -/
lemma spanRightCollapse_left : horn₂₀.ι₀₁ ≫ spanRightCollapse.{u} =
    SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 第二枝は元の標準区間そのもの。 -/
lemma spanRightCollapse_right : horn₂₀.ι₀₂ ≫ spanRightCollapse.{u} = 𝟙 Δ[1] := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 恒等な第一枝の span の指定全余錐は、元の第二枝の終点を余極限とする。 -/
lemma spanRightCollapse_edgeTarget_isColimit {C : SSet.{u}} [Quasicategory C]
    (g : (Δ[1] : SSet.{u}) ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeTargetCocone g).restrict spanRightCollapse) := by
  have ha := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.terminalPoint_rightAnodyne (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.stdSimplex_last_isTerminalVertex.{u} 1)
  have he : SSet.yonedaEquiv.symm
      (stdSimplex.obj₀Equiv.symm (Fin.last 1)) = (stdSimplex.δ (0 : Fin 2) :
        (Δ[0] : SSet.{u}) ⟶ Δ[1]) := by
    apply SSet.yonedaEquiv.injective
    decide
  rw [he] at ha
  have ht := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_rightAnodyne _ ha
  have hg : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeTargetCocone g) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isColimitCone_iff_restrict_rightCofinal _ ht (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeTargetCocone g)).mpr
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeTargetCocone_target_isColimit g)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isColimitCone_iff_restrict_rightCofinal spanRightCollapse
    spanRightCollapse_isRightCofinal (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeTargetCocone g)).mp hg

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
