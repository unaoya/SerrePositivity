module

public import SerrePositivity.InfinityCategories.F2.Ind.TerminalSubcomplexCofinal

/-!
概要：小さい κ-filtered ∞ 圏には、小さい通常の κ-filtered poset からの cofinal map がある。
方針：κ と同じ濃度のラベルを取り、構成済みの小さい終頂点付き部分複体の包含順を使う。
規約：元の ∞ 圏を標的にし、通常の κ-filtered 性と cofinal 性を両方証明する。
使われ方：一般の coherent な前層図式の添字を strict な図式へ移す工程。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 小さい κ-filtered ∞ 圏には、小さい通常の κ-filtered poset による cofinal な添字がある。 -/
lemma exists_cofinal_cardinalFiltered_poset {κ : Cardinal.{u}} [Fact κ.IsRegular]
    (C : SSet.{u}) [Quasicategory C] [IsKappaFiltered κ C] :
    ∃ (I : Type u) (o : PartialOrder I),
      letI := o
      ∃ f : nerve I ⟶ C, IsCardinalFiltered I κ ∧ IsRightCofinal f := by
  have hκ : κ.IsRegular := Fact.out
  let T := κ.out
  have hT : κ ≤ Cardinal.mk T := by rw [Cardinal.mk_out]
  let I := SmallSubcomplexFamily κ (C ⊗ nerve (Codiscrete T)) (terminalSubcomplexPredicate _)
  refine ⟨I, inferInstance, terminalSubcomplexBaseMap κ C T, ?_, ?_⟩
  · exact terminalSubcomplexFamily_isCardinalFiltered hT
  · exact terminalSubcomplexBaseMap_isRightCofinal hκ hT

end SerrePositivity.InfinityCategories.F2.Ind
