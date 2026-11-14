module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Completion
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.FunctorHomReflection
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.TerminalPointAnodyne
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConstantFunctor
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakReverseHomotopy
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorEdgeFromPrism

/-!
概要：終対象を持つ冪等完備化の元の底は弱可縮。
方針：終対象から像への retract の包含と全終対象収縮を合成し、充満忠実性で戻す。
規約：全関手上のホモトピーを使用し、ホモトピー圏の対象の議論だけで代用しない。
使われ方：HTT 5.1.4.5 の双対、slice 上の Quillen A。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 終対象が像の指定対象の retract なら、元の底の恒等から定値への全収縮が存在する。 -/
lemma terminalRetract_contraction_exists {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (f : C ⟶ D) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f)
    (c : C _⦋0⦌) (b : D _⦋0⦌) (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex b)
    (r : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.VertexRetraction b (f.app (Opposite.op ⦋0⦌) c)) :
    Nonempty (SSet.Homotopy (𝟙 C) (SSet.const c)) := by
  obtain ⟨H, h₀, h₁, _hfix⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.exists_fixed_terminal_prism hb
  let Hf := (Δ[1] ◁ f) ≫ H
  have h₀f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 C ≫ Hf = f := by
    dsimp only [Hf]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, h₀, Category.comp_id]
  have h₁f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 C ≫ Hf = SSet.const b := by
    dsimp only [Hf]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, h₁, SSet.comp_const]
  let e := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorEdgeFromPrism Hf h₀f h₁f
  obtain ⟨a, _ha⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective b
    (f.app (Opposite.op ⦋0⦌) c) r.i
  have ac := a.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap C D))
  change SSet.Truncated.Edge (X := (truncation 2).obj ((ihom C).obj D))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap C D).app (Opposite.op ⦋0⦌) b)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap C D).app (Opposite.op ⦋0⦌)
      (f.app (Opposite.op ⦋0⦌) c)) at ac
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap_vertex] at ac
  let K := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge (e.comp ac)
  have KK : SSet.Homotopy ((𝟙 C) ≫ f) ((SSet.const c) ≫ f) := by
    rw [Category.id_comp, SSet.const_comp]
    exact K
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.homotopy_exists_of_fullyFaithful f hf (𝟙 C) (SSet.const c) KK

/-- 終対象が像の対象の retract である充満忠実な底は、弱可縮。 -/
lemma isWeaklyContractible_of_terminalRetract {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (f : C ⟶ D) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f)
    (c : C _⦋0⦌) (b : D _⦋0⦌) (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex b)
    (r : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.VertexRetraction b (f.app (Opposite.op ⦋0⦌) c)) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible C := by
  obtain ⟨H⟩ := terminalRetract_contraction_exists f hf c b hb r
  let g : (⊤_ SSet.{u}) ⟶ C := SSet.const c
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isWeakHomotopyEquivalence_of_reverseHomotopyInverse (terminal.from C) g
  · change SSet.Homotopy (𝟙 C) (_ ≫ SSet.const c)
    rw [SSet.comp_const]
    exact H
  · have h : g ≫ terminal.from C = 𝟙 _ := terminal.hom_ext _ _
    rw [h]
    exact SSet.RelativeMorphism.Homotopy.refl (SSet.RelativeMorphism.botEquiv.symm (𝟙 _))

/-- 終対象を持つ冪等完備化の元の底は弱可縮。 -/
lemma IsIdempotentCompletion.isWeaklyContractible_of_terminal {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (f : C ⟶ D) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f)
    (b : D _⦋0⦌) (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex b) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible C := by
  obtain ⟨c, ⟨r⟩⟩ := hf.2.2 b
  exact isWeaklyContractible_of_terminalRetract f hf.2.1 c b hb r

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "5.1.4.5"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.isWeaklyContractible_of_terminal
