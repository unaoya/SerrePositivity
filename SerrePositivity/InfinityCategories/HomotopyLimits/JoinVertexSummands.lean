module

public import SerrePositivity.InfinityCategories.Core.Join

/-!
概要：join の各頂点を、元のどちらか一方の因子の頂点として回収する。
方針：零単体の切断を零と一に分ける。
規約：空の因子や充填性を仮定しない。
使われ方：全錐の円柱の可逆性を元の頂点比較と図式の成分比較から証明する。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の join の各頂点は、元の左因子または右因子の頂点の像。 -/
lemma joinVertexSummands {A B : SSet.{u}} (s : (join A B) _⦋0⦌) :
    (∃ a : A _⦋0⦌, (joinInl A B).app (Opposite.op ⦋0⦌) a = s) ∨
      (∃ b : B _⦋0⦌, (joinInr A B).app (Opposite.op ⦋0⦌) b = s) := by
  rcases s with ⟨i, x, y⟩
  fin_cases i
  · right
    refine ⟨y, ?_⟩
    cases x
    rfl
  · left
    refine ⟨x, ?_⟩
    cases y
    rfl

end SerrePositivity.InfinityCategories.HomotopyLimits
