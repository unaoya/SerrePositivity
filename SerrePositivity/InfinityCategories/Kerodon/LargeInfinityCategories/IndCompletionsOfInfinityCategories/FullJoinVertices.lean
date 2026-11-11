module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.FullSubcomplexFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceMap

/-!
概要：join からの全図式の頂点条件を、同じ左右の二因子の頂点条件で確認する。
方針：零単体の切断は左右いずれかだけなので、二つの包含で検査する。
規約：図式・頂点条件に充填性を要求しない。
使われ方：Ind 内の全余錐を元の前層余錐から持ち上げる。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 同じ join 全図式の頂点条件は、左右の制限で検査できる。 -/
lemma join_vertices_property {K A X : SSet.{u}} (P : X _⦋0⦌ → Prop)
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K A ⟶ X)
    (hK : ∀ k, P ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K A ≫ f).app (Opposite.op ⦋0⦌) k))
    (hA : ∀ a, P ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K A ≫ f).app (Opposite.op ⦋0⦌) a)) :
    ∀ z, P (f.app (Opposite.op ⦋0⦌) z) := by
  rintro ⟨l, k, a⟩
  fin_cases l
  · cases k
    exact hA a
  · cases a
    exact hK k

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
