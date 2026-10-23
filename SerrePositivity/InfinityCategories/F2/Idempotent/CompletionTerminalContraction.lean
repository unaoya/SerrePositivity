module

public import SerrePositivity.InfinityCategories.F2.Idempotent.Completion
public import SerrePositivity.InfinityCategories.F2.Idempotent.FunctorHomReflection
public import SerrePositivity.InfinityCategories.F1B.KanTerminalPointAnodyne
public import SerrePositivity.InfinityCategories.F1B.ConstantFunctor
public import SerrePositivity.InfinityCategories.F1B.WeakReverseHomotopy
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorEdgeFromPrism

/-!
概要：終対象を持つ冪等完備化の元の底は弱可縮。
方針：終対象から像への retract の包含と全終対象収縮を合成し、充満忠実性で戻す。
規約：全関手上のホモトピーを使用し、ホモトピー圏の対象の議論だけで代用しない。
使われ方：HTT 5.1.4.5 の双対、slice 上の Quillen A。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 終対象が像の指定対象の retract なら、元の底の恒等から定値への全収縮が存在する。 -/
lemma terminalRetract_contraction_exists {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (f : C ⟶ D) (hf : IsFullyFaithful f)
    (c : C _⦋0⦌) (b : D _⦋0⦌) (hb : IsTerminalVertex b)
    (r : VertexRetraction b (f.app (Opposite.op ⦋0⦌) c)) :
    Nonempty (SSet.Homotopy (𝟙 C) (SSet.const c)) := by
  obtain ⟨H, h₀, h₁, _hfix⟩ := F1B.kanExists_fixed_terminal_prism hb
  let Hf := (Δ[1] ◁ f) ≫ H
  have h₀f : prismEndpoint 0 C ≫ Hf = f := by
    dsimp only [Hf]
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, h₀, Category.comp_id]
  have h₁f : prismEndpoint 1 C ≫ Hf = SSet.const b := by
    dsimp only [Hf]
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, h₁, SSet.comp_const]
  let e := functorEdgeFromPrism Hf h₀f h₁f
  obtain ⟨a, _ha⟩ := homotopyCategory_homMk_surjective b
    (f.app (Opposite.op ⦋0⦌) c) r.i
  have ac := a.map ((truncation 2).map (constantFunctorMap C D))
  change SSet.Truncated.Edge (X := (truncation 2).obj ((ihom C).obj D))
    ((constantFunctorMap C D).app (Opposite.op ⦋0⦌) b)
    ((constantFunctorMap C D).app (Opposite.op ⦋0⦌)
      (f.app (Opposite.op ⦋0⦌) c)) at ac
  rw [constantFunctorMap_vertex, constantFunctorMap_vertex] at ac
  let K := simplicialHomotopyOfFunctorEdge (e.comp ac)
  have KK : SSet.Homotopy ((𝟙 C) ≫ f) ((SSet.const c) ≫ f) := by
    rw [Category.id_comp, SSet.const_comp]
    exact K
  exact homotopy_exists_of_fullyFaithful f hf (𝟙 C) (SSet.const c) KK

/-- 終対象が像の対象の retract である充満忠実な底は、弱可縮。 -/
lemma isWeaklyContractible_of_terminalRetract {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (f : C ⟶ D) (hf : IsFullyFaithful f)
    (c : C _⦋0⦌) (b : D _⦋0⦌) (hb : IsTerminalVertex b)
    (r : VertexRetraction b (f.app (Opposite.op ⦋0⦌) c)) : IsWeaklyContractible C := by
  obtain ⟨H⟩ := terminalRetract_contraction_exists f hf c b hb r
  let g : (⊤_ SSet.{u}) ⟶ C := SSet.const c
  apply isWeakHomotopyEquivalence_of_reverseHomotopyInverse (terminal.from C) g
  · change SSet.Homotopy (𝟙 C) (_ ≫ SSet.const c)
    rw [SSet.comp_const]
    exact H
  · have h : g ≫ terminal.from C = 𝟙 _ := terminal.hom_ext _ _
    rw [h]
    exact SSet.RelativeMorphism.Homotopy.refl (SSet.RelativeMorphism.botEquiv.symm (𝟙 _))

/-- 終対象を持つ冪等完備化の元の底は弱可縮。 -/
lemma IsIdempotentCompletion.isWeaklyContractible_of_terminal {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (f : C ⟶ D) (hf : IsIdempotentCompletion f)
    (b : D _⦋0⦌) (hb : IsTerminalVertex b) : IsWeaklyContractible C := by
  obtain ⟨c, ⟨r⟩⟩ := hf.2.2 b
  exact isWeaklyContractible_of_terminalRetract f hf.2.1 c b hb r

end SerrePositivity.InfinityCategories.F2.Idempotent
