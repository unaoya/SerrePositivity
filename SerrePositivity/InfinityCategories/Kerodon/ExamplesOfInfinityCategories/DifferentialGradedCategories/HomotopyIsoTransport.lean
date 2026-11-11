module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceCalculus

/-!
# 単体集合の同型によるホモトピー同値性の移送

概要：単体集合の同型は実際の単体的ホモトピー逆を持ち、Kan 複体間の後合成で同値性を保つ。
方針：同型の両逆則を定値ホモトピーにし、Core の合成則を使う。
規約：同型自体には Kan 性不要。合成則で三つの Kan 複体を仮定する。
使われ方：HA 1.3.1.17、Kerodon 2.5.9（Tag 00SC） の標準 DK 座標から実際の pinched Hom への移送。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory

/-- 概要：単体集合の同型は実際の単体的ホモトピー逆を持つ。
方針：逆同型を逆射とし、両合成の恒等式を定値ホモトピーにする。
規約：充填性や弱同値の仮定は不要。
使われ方：Kerodon 2.5.9（Tag 00SC） の写像空間の座標模型の変更。 -/
lemma simplicialHomotopyEquivalence_iso_hom {A B : SSet.{u}} (e : A ≅ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence e.hom := by
  refine ⟨e.inv, ?_, ?_⟩
  · rw [e.hom_inv_id]
    exact ⟨SSet.RelativeMorphism.Homotopy.refl (SSet.RelativeMorphism.botEquiv.symm (𝟙 A))⟩
  · rw [e.inv_hom_id]
    exact ⟨SSet.RelativeMorphism.Homotopy.refl (SSet.RelativeMorphism.botEquiv.symm (𝟙 B))⟩

/-- 概要：Kan 複体間の射のホモトピー同値性は後合成の単体集合同型で変わらない。
方針：同型のホモトピー逆と合成し、片側では逆同型を戻して相殺する。
規約：実際のホモトピー逆の存在を両側で主張する。
使われ方：HA 1.3.1.17 の標準座標での証明を実際の写像空間へ戻す。 -/
lemma simplicialHomotopyEquivalence_postcomp_iso_iff {A B C : SSet.{u}}
    [SSet.KanComplex A] [SSet.KanComplex B] [SSet.KanComplex C] (f : A ⟶ B) (e : B ≅ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (f ≫ e.hom) ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence f := by
  constructor
  · intro h
    have h' := h.comp (simplicialHomotopyEquivalence_iso_hom e.symm)
    simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id] using h'
  · intro h
    exact h.comp (simplicialHomotopyEquivalence_iso_hom e)

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
