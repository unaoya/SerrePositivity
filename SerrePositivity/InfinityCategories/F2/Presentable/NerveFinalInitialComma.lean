module

public import SerrePositivity.InfinityCategories.F2.Presentable.SmallFilteredTotalCofinal
public import SerrePositivity.InfinityCategories.F1B.Cofinality.Cofinality

/-!
概要：通常の各右 comma に始対象を構成して、同じ nerve 写像の right cofinal 性を得る。
方針：始対象による弱可縮性を F1B の native な comma 同型で移し、Quillen A を適用する。
規約：通常の Final instance や cofinal 性を仮定せず、各始対象のデータを明示引数とする。
使われ方：部分添字 fiber から左 Kan 局所添字への比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 通常の各 comma の明示的な始対象は、元の nerve 写像の right cofinal 性を与える。 -/
lemma nerveMap_isRightCofinal_of_initial_comma {P Q : Type u}
    [Category.{u} P] [Category.{u} Q] (F : P ⥤ Q)
    (h : ∀ q : Q, ∃ c : StructuredArrow q F, Nonempty (IsInitial c)) :
    IsRightCofinal (nerveMap F) := by
  apply isRightCofinal_of_weaklyContractible_coslices
  intro v
  obtain ⟨q, rfl⟩ := nerveEquiv.symm.surjective v
  obtain ⟨c, ⟨hc⟩⟩ := h q
  have h0 : IsContractibleKan (Δ[0] : SSet.{u}) := by
    intro n b
    exact ⟨stdSimplex.isTerminalObj₀.from _, stdSimplex.isTerminalObj₀.hom_ext _ _⟩
  have hcomma : IsWeaklyContractible (nerve (StructuredArrow q F)) :=
    (nervePoint_isLeftCofinal hc).isWeakHomotopyEquivalence.weaklyContractible_iff.mp
      h0.isWeaklyContractible
  let e := SerrePositivity.InfinityCategories.F1B.nerveRightKanShapeIso q F ≪≫ pullbackSymmetry _ _
  exact (qCatEquivalenceOfIso e).isQCatEquivalence.isWeakHomotopyEquivalence
    |>.weaklyContractible_iff.mp hcomma

end SerrePositivity.InfinityCategories.F2.Presentable
