module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.SmallSimplicialShapes

/-!
概要：κ-small な形状の頂点には κ 個未満のラベルしか現れず、大きいラベル集合には未使用点がある。
方針：零単体を元の非退化単体へ単射し、ラベル写像の非全射性を濃度で示す。
規約：κ の正則性は不要。全次数の小ささと零単体数を混同しない。
使われ方：小さい部分複体の錐を新しい頂点ラベルで単射に埋め込む構成。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
universe u
open SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- κ-small な形状の頂点の濃度は κ 未満。 -/
lemma cardinal_vertices_lt_of_isKappaSmall {κ : Cardinal.{u}} {K : SSet.{u}}
    (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ K) : Cardinal.mk (K _⦋0⦌) < κ := by
  let f : K _⦋0⦌ → K.N := fun x => N.mk x (by simp)
  have hf : Function.Injective f := fun x y h =>
    (S.ext_iff x y).mp (congrArg N.toS h)
  exact lt_of_le_of_lt (Cardinal.mk_le_of_injective hf) hK

/-- κ 以上の濃度を持つラベル集合には、同じ小さい形状の頂点に現れないラベルがある。 -/
lemma exists_fresh_vertex_label {κ : Cardinal.{u}} {K : SSet.{u}} (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ K)
    {A : Type u} (hA : κ ≤ Cardinal.mk A) (f : K _⦋0⦌ → A) :
    ∃ a : A, ∀ x, f x ≠ a := by
  by_contra! h
  have hf : Function.Surjective f := h
  exact (not_lt_of_ge (hA.trans (Cardinal.mk_le_of_surjective hf)))
    (cardinal_vertices_lt_of_isKappaSmall hK)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
