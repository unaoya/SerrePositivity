module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentTriangleLastSimplexHead
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentTriangleLastSimplexTail

/-!
概要：最大化側の最後辺と、元の二辺の全係数作用の実単体を厳密に一致させる。
方針：同じ対象表示の head・tail と初点の自己 Hom を比較し、空 Hom は path で除く。
規約：元の全次数の係数と全 Hom を保持する。
使われ方：Ncomp の二つの実 pointed prism 自体の一致。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet SimplicialThickening
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 概要：同じ元の二辺と全係数から作った実単体は全 Hom を保って一致する。
方針：初点と正頂点の四分岐で外延性を適用する。
規約：元の全次数の係数を保持。使われ方：実 prism の全次数の一致。 -/
lemma coherentTriangleLastSimplex_eq (s : SpaceInfinity.{u} _⦋2⦌)
    {n : ℕ} (α : ⦋n⦌ ⟶ ⦋1⦌)
    (p : (SimplicialCategory.sHom pointKanObject (s.obj ⟨ULift.up 0⟩)).op _⦋n⦌) :
    coherentTriangleLastSourceSimplex s α p = coherentTriangleLastCompositeSimplex s α p := by
  refine EnrichedFunctor.ext SSet
    (fun a ↦ coherentTriangleLastSimplex_obj s α p a.as.down) (fun a b ↦ ?_)
  rcases a with ⟨⟨a⟩⟩
  rcases b with ⟨⟨b⟩⟩
  induction a using Fin.cases <;> induction b using Fin.cases
  case zero.zero =>
    exact thickeningSelfHom_comparison (C := KanObject.{u})
      (coherentTriangleLastSourceSimplex s α p) (coherentTriangleLastCompositeSimplex s α p)
      ⟨ULift.up 0⟩ (coherentTriangleLastSimplex_obj s α p 0)
  case zero.succ b => exact coherentTriangleLastSimplex_head s α p b
  case succ.zero a =>
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro P
    have h := Path.le (P.obj 0)
    change a.succ ≤ 0 at h
    simp at h
  case succ.succ a b => exact coherentTriangleLastSimplex_tail s α p a b

end SerrePositivity.InfinityCategories.F2
