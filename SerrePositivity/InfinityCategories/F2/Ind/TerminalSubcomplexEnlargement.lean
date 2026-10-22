module

public import SerrePositivity.InfinityCategories.F2.Ind.ConeApexTerminal
public import SerrePositivity.InfinityCategories.F2.Ind.SmallCodiscreteConeRange
public import SerrePositivity.InfinityCategories.Core.TerminalMap

/-!
概要：ラベル付き積の任意の小さい部分複体は、小さい終頂点付き部分複体に含まれる。
方針：同じ単射な錐の像への同型で終頂点を移す。
規約：左因子の底だけに κ-filtered 性を仮定し、部分複体の充填性は仮定しない。
使われ方：終頂点付き部分複体の κ-filtered な被覆。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 単射な右錐の像は同じ右頂点を終頂点に持つ。 -/
lemma coneRange_hasTerminalVertex {K X : SSet.{u}} (f : join K Δ[0] ⟶ X) [Mono f] :
    ∃ x : (Subcomplex.range f).toSSet _⦋0⦌, IsTerminalVertex x :=
  ⟨(Subfunctor.toRange f).app _ (coneApex K),
    (coneApex_isTerminalVertex K).map_of_isIso (Subfunctor.toRange f)⟩

/-- 元の小さい部分複体を含む、同じ積内の小さい終頂点付き部分複体が存在する。 -/
lemma exists_small_terminalSubcomplex {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    {C : SSet.{u}} [Quasicategory C] [IsKappaFiltered κ C]
    {T : Type u} (hT : κ ≤ Cardinal.mk T)
    (A : (C ⊗ nerve (Codiscrete T)).Subcomplex) (hA : IsKappaSmall κ A.toSSet) :
    ∃ B : (C ⊗ nerve (Codiscrete T)).Subcomplex, IsKappaSmall κ B.toSSet ∧
      (∃ x : B.toSSet _⦋0⦌, IsTerminalVertex x) ∧ A ≤ B := by
  obtain ⟨d, hd, hsmall, hAB, _⟩ := exists_small_codiscreteConeRange hκ hT A hA
  let := hd
  exact ⟨Subcomplex.range d.val, hsmall, coneRange_hasTerminalVertex d.val, hAB⟩

end SerrePositivity.InfinityCategories.F2.Ind
