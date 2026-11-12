module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorInitial
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakReverseHomotopy
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.WeakContractibility
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：始対象または終対象を持つ単体集合の弱可縮性。
方針：関手単体集合の定値関手の始対象性・終対象性から全体の収縮を得る。
規約：弱可縮性は全 Kan 標的へのホモトピー類で検査し、元の Kan 性を要求しない。
使われ方：Kerodon Corollary 4.7.3.23（Tag 02P2）、Theorem 7.2.3.1（Tag 02NY） の必要性。

対応節は Kerodon 4.7（Tag 05EA）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories

/-- 概要：始対象を持つ単体集合は一点へ実際の単体的ホモトピーで収縮する。
方針：定値始対象関手から恒等関手への辺を uncurry する。
規約：X の quasicategory 性を要求しない。
使われ方：Kerodon Corollary 4.7.3.23（Tag 02P2） の始対象の場合。 -/
lemma IsInitialVertex.terminalFrom_isSimplicialHomotopyEquivalence
    {X : SSet.{u}} {x : X _⦋0⦌} (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (terminal.from X) := by
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const x : X ⟶ X)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isInitialVertex_functorVertex_of_pointwise _ (fun _ ↦ by
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 0)
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
      exact hx)
  obtain ⟨e⟩ := ht.nonempty_edge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 X))
  let g : (⊤_ SSet.{u}) ⟶ X := SSet.const x
  have h₀ : terminal.from X ≫ g = (SSet.const x : X ⟶ X) := SSet.comp_const _ _
  have h₁ : g ≫ terminal.from X = 𝟙 _ := terminal.hom_ext _ _
  refine ⟨g, ?_, ?_⟩
  · rw [h₀]
    exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge e⟩
  · rw [h₁]
    exact ⟨SSet.RelativeMorphism.Homotopy.refl (SSet.RelativeMorphism.botEquiv.symm (𝟙 _))⟩

/-- 概要：始対象を持つ単体集合は弱可縮。
方針：一点への射の実際のホモトピー逆から弱同値性を得る。
規約：元の単体集合に Kan 性を要求しない。
使われ方：Kerodon Corollary 4.7.3.23（Tag 02P2）、Quillen A の coslice の弱可縮性。 -/
@[kerodon 02P2]
lemma IsInitialVertex.isWeaklyContractible {X : SSet.{u}} {x : X _⦋0⦌}
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex x) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible X :=
  hx.terminalFrom_isSimplicialHomotopyEquivalence.isWeakHomotopyEquivalence

/-- 概要：終対象を持つ単体集合は弱可縮。
方針：恒等関手から定値終対象関手へのホモトピーを、Kan 標的への前合成で逆にする。
規約：元の X 内でホモトピーを逆向きにできるという仮定は加えない。
使われ方：Kerodon Corollary 4.7.3.23（Tag 02P2） の終対象の場合。 -/
@[kerodon 02P2]
lemma IsTerminalVertex.isWeaklyContractible {X : SSet.{u}} {x : X _⦋0⦌}
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible X := by
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const x : X ⟶ X)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isTerminalVertex_functorVertex_of_pointwise _ (fun _ ↦ by
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 0)
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
      exact hx)
  obtain ⟨e⟩ := ht.nonempty_edge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 X))
  let g : (⊤_ SSet.{u}) ⟶ X := SSet.const x
  have h₀ : terminal.from X ≫ g = (SSet.const x : X ⟶ X) := SSet.comp_const _ _
  have h₁ : g ≫ terminal.from X = 𝟙 _ := terminal.hom_ext _ _
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isWeakHomotopyEquivalence_of_reverseHomotopyInverse (terminal.from X) g
  · rw [h₀]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge e
  · rw [h₁]
    exact SSet.RelativeMorphism.Homotopy.refl (SSet.RelativeMorphism.botEquiv.symm (𝟙 _))

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
