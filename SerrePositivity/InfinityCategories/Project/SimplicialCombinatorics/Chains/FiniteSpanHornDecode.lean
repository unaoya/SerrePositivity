module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Chains.FiniteSpanNerveCode

/-!
概要：標準 span ホーンの全単体を、同じ三点の半順序の鎖へ復号する。
方針：ホーンの単体は二つの終点の一方を欠くので、復号した頂点列は単調。
規約：退化単体も含め、元の単体の全頂点番号を保持する。
使われ方：標準 span と有限半順序 nerve の厳密な同型。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-- span ホーンの頂点列を復号すると、有限半順序の鎖になる。 -/
lemma finiteSpanHornDecode_monotone {n : SimplexCategoryᵒᵖ}
    (s : (horn 2 0 : SSet.{u}).obj n) :
    Monotone (fun v => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.finiteSpanDecode.{u} ((stdSimplex.objEquiv s.val).toOrderHom v)) := by
  intro i j hij
  let σ := (stdSimplex.objEquiv s.val).toOrderHom
  have hc : σ i = 0 ∨ σ i = σ j := by
    obtain ⟨k, hk, hm⟩ := (mem_horn_iff_notMem_range s.val (0 : Fin 3)).mp s.property
    have hi : σ i ≠ k := fun he => hm ⟨i, he⟩
    have hj : σ j ≠ k := fun he => hm ⟨j, he⟩
    have hle := σ.monotone hij
    have hk0 : k.val ≠ 0 := fun he => hk (Fin.ext he)
    have hi' : (σ i).val ≠ k.val := fun he => hi (Fin.ext he)
    have hj' : (σ j).val ≠ k.val := fun he => hj (Fin.ext he)
    have hi3 : (σ i).val < 3 := (σ i).isLt
    have hj3 : (σ j).val < 3 := (σ j).isLt
    have hk3 : k.val < 3 := k.isLt
    have hv : (σ i).val = 0 ∨ (σ i).val = (σ j).val := by omega
    exact hv.imp Fin.ext Fin.ext
  change (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.finiteSpanDecode (σ i)).down = .zero ∨
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.finiteSpanDecode (σ i)).down = (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.finiteSpanDecode (σ j)).down
  rcases hc with h | h
  · rw [h]
    exact Or.inl rfl
  · rw [h]
    exact Or.inr rfl

/-- 標準 span ホーンから有限半順序 nerve への実際の全単体写像。 -/
def finiteSpanHornToNerve : (horn 2 0 : SSet.{u}) ⟶ nerve _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FiniteSpanIndex.{u} where
  app n := ↾fun s => (⟨fun v => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.finiteSpanDecode
    ((stdSimplex.objEquiv s.val).toOrderHom v), finiteSpanHornDecode_monotone s⟩ :
      Fin (n.unop.len + 1) →o _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FiniteSpanIndex).monotone.functor
  naturality := by
    intro n m α
    apply ConcreteCategory.hom_ext
    intro s
    apply CategoryTheory.nerve.ext_of_isThin
    funext k
    rfl

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
