module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CosliceFiberSplitRestriction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.StdSimplexTerminal
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.TerminalPointAnodyne

/-!
概要：coslice の左の一点を任意の反転標準単体へ広げても、固定終点の写像空間は同値。
方針：標準単体の終点への制限を右 anodyne な切断として使い、反転の同型で移す。
規約：実際の形の崩壊への制限写像を保ち、標準単体そのものを圏同値とみなさない。
使われ方：twisted arrow の両半分固定の模型を、各行で同値な二重単体図式にする。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration

/-- 左の反転標準単体を一点へ潰す形の射。 -/
def cosliceSimplexCollapse (n : SimplexCategory) : (stdSimplex.{u}.obj n).op ⟶ Δ[0] :=
  stdSimplex.isTerminalObj₀.from _

/-- 標準単体の終点は反転後の標準単体にも右 anodyne な切断を与える。 -/
lemma exists_cosliceSimplexCollapse_rightAnodyne_section (n : ℕ) :
    ∃ v : (Δ[0] : SSet.{u}) ⟶ (Δ[n] : SSet.{u}).op,
      Mono v ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions v ∧ v ≫ cosliceSimplexCollapse ⦋n⦌ = 𝟙 _ := by
  let j := SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (Fin.last n))
  have hj := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.terminalPoint_rightAnodyne (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.stdSimplex_last_isTerminalVertex.{u} n)
  have hm : Mono j := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalPointInclusion_mono _
  let v := j ≫ (stdSimplex.opIso.{u} ⦋n⦌).inv
  have : Mono v := by dsimp [v]; infer_instance
  exact ⟨v, inferInstance, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions.comp_mem _ _ hj
    (MorphismProperty.of_isIso _ _), stdSimplex.isTerminalObj₀.hom_ext _ _⟩

/-- 固定した左の標準単体の大きさごとに、元の coslice fiber の実際の拡張写像は同値。 -/
lemma cosliceSimplexExpansion_isQCatEquivalence {C : SSet.{u}} [Quasicategory C]
    (x y : C _⦋0⦌) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap (SSet.yonedaEquiv.symm x)
      (cosliceSimplexCollapse.{u} ⦋n⦌) y) := by
  obtain ⟨v, hm, hv, hf⟩ := exists_cosliceSimplexCollapse_rightAnodyne_section.{u} n
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceRestrictionFiberMap_isQCatEquivalence_of_rightAnodyne_section x y _ v hv hf

/-- 崩壊後の左の固定図式は、元の頂点に定値となる。 -/
lemma cosliceSimplexCollapse_comp_yoneda {C : SSet.{u}} (x : C _⦋0⦌)
    (n : SimplexCategory) :
    cosliceSimplexCollapse n ≫ SSet.yonedaEquiv.symm x = SSet.const x := by
  have h : cosliceSimplexCollapse.{u} n =
      SSet.const (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))) := stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [h, SSet.const_comp]
  have hp := SSet.yonedaEquiv_comp (𝟙 (Δ[0] : SSet.{u})) (SSet.yonedaEquiv.symm x)
  have he : (SSet.yonedaEquiv.symm x).app (Opposite.op ⦋0⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))) = x := by
    simpa only [Category.id_comp, Equiv.apply_symm_apply] using hp.symm
  exact congrArg SSet.const he

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
