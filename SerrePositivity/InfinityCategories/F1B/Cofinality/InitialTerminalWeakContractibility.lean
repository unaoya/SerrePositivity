module

public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorInitial
public import SerrePositivity.InfinityCategories.F1B.Homotopy.WeakReverseHomotopy
public import SerrePositivity.InfinityCategories.F1B.Homotopy.WeakContractibility

/-!
概要：始対象または終対象を持つ単体集合の弱可縮性。
方針：関手単体集合の定値関手の始対象性・終対象性から全体の収縮を得る。
規約：弱可縮性は全 Kan 標的へのホモトピー類で検査し、元の Kan 性を要求しない。
使われ方：Kerodon Corollary 4.7.3.23、Theorem 7.2.3.1 の必要性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：始対象を持つ単体集合は一点へ実際の単体的ホモトピーで収縮する。
方針：定値始対象関手から恒等関手への辺を uncurry する。
規約：X の quasicategory 性を要求しない。
使われ方：Kerodon Corollary 4.7.3.23 の始対象の場合。 -/
lemma IsInitialVertex.terminalFrom_isSimplicialHomotopyEquivalence
    {X : SSet.{u}} {x : X _⦋0⦌} (hx : IsInitialVertex x) :
    IsSimplicialHomotopyEquivalence (terminal.from X) := by
  have ht : IsInitialVertex (functorVertex (SSet.const x : X ⟶ X)) :=
    isInitialVertex_functorVertex_of_pointwise _ (fun _ ↦ by
      change IsInitialVertex (PinchedHom.constant x 0)
      rw [pinchedConstant_zero]
      exact hx)
  obtain ⟨e⟩ := ht.nonempty_edge (functorVertex (𝟙 X))
  let g : (⊤_ SSet.{u}) ⟶ X := SSet.const x
  have h₀ : terminal.from X ≫ g = (SSet.const x : X ⟶ X) := SSet.comp_const _ _
  have h₁ : g ≫ terminal.from X = 𝟙 _ := terminal.hom_ext _ _
  refine ⟨g, ?_, ?_⟩
  · rw [h₀]
    exact ⟨simplicialHomotopyOfFunctorEdge e⟩
  · rw [h₁]
    exact ⟨SSet.RelativeMorphism.Homotopy.refl (SSet.RelativeMorphism.botEquiv.symm (𝟙 _))⟩

/-- 概要：始対象を持つ単体集合は弱可縮。
方針：一点への射の実際のホモトピー逆から弱同値性を得る。
規約：元の単体集合に Kan 性を要求しない。
使われ方：Kerodon Corollary 4.7.3.23、Quillen A の coslice の弱可縮性。 -/
lemma IsInitialVertex.isWeaklyContractible {X : SSet.{u}} {x : X _⦋0⦌}
    (hx : IsInitialVertex x) : IsWeaklyContractible X :=
  hx.terminalFrom_isSimplicialHomotopyEquivalence.isWeakHomotopyEquivalence

/-- 概要：終対象を持つ単体集合は弱可縮。
方針：恒等関手から定値終対象関手へのホモトピーを、Kan 標的への前合成で逆にする。
規約：元の X 内でホモトピーを逆向きにできるという仮定は加えない。
使われ方：Kerodon Corollary 4.7.3.23 の終対象の場合。 -/
lemma IsTerminalVertex.isWeaklyContractible {X : SSet.{u}} {x : X _⦋0⦌}
    (hx : IsTerminalVertex x) : IsWeaklyContractible X := by
  have ht : IsTerminalVertex (functorVertex (SSet.const x : X ⟶ X)) :=
    isTerminalVertex_functorVertex_of_pointwise _ (fun _ ↦ by
      change IsTerminalVertex (PinchedHom.constant x 0)
      rw [pinchedConstant_zero]
      exact hx)
  obtain ⟨e⟩ := ht.nonempty_edge (functorVertex (𝟙 X))
  let g : (⊤_ SSet.{u}) ⟶ X := SSet.const x
  have h₀ : terminal.from X ≫ g = (SSet.const x : X ⟶ X) := SSet.comp_const _ _
  have h₁ : g ≫ terminal.from X = 𝟙 _ := terminal.hom_ext _ _
  apply isWeakHomotopyEquivalence_of_reverseHomotopyInverse (terminal.from X) g
  · rw [h₀]
    exact simplicialHomotopyOfFunctorEdge e
  · rw [h₁]
    exact SSet.RelativeMorphism.Homotopy.refl (SSet.RelativeMorphism.botEquiv.symm (𝟙 _))

end SerrePositivity.InfinityCategories
