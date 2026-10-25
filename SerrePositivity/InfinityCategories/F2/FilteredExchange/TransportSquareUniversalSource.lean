module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.TransportSquareDataEquality

/-!
概要：任意の始点族での元の四角形比較を、一つの普遍始点族の制限で表す。
方針：始点 fiber と元の係数の直積上で構成し、同じ始点のグラフへ制限する。
規約：任意の係数と元の指定値を保持。使われ方：始点同型への自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 普遍始点の係数図式を始点の同じグラフへ制限すると、元の実四角形に一致する。 -/
lemma transportIntervalSquare_universalSource_reindex {E B P : SSet.{u}}
    (p : E ⟶ B) {a b c d : B _⦋0⦌} (s : TransportIntervalSquare P a b c d)
    (f : P ⟶ vertexFiber p a) :
    (s.precomp (snd (vertexFiber p a) P)).precomp (lift f (𝟙 P)) = s := by
  apply transportIntervalSquare_eq_of_data
  all_goals dsimp only [TransportIntervalSquare.precomp]
  · rw [← Category.assoc, lift_snd, Category.id_comp]
  · rw [← Category.assoc, lift_snd, Category.id_comp]
  · rw [← Category.assoc, lift_snd, Category.id_comp]
  · rw [← Category.assoc, lift_snd, Category.id_comp]
  · rw [← Category.assoc, ← whiskerLeft_comp, ← whiskerLeft_comp, lift_snd,
      whiskerLeft_id, whiskerLeft_id, Category.id_comp]

/-- 任意の元の始点族での指定比較は、一つの普遍始点比較の同じグラフ制限である。 -/
lemma transportIntervalSquare_transportIso_universal_precomp_heq {E B P : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b c d : B _⦋0⦌}
    (s : TransportIntervalSquare P a b c d) (f : P ⟶ vertexFiber p a) :
    HEq (((s.precomp (snd (vertexFiber p a) P)).transportIso p
      (fst (vertexFiber p a) P)).precomp (lift f (𝟙 P))) (s.transportIso p f) := by
  have h := transportIntervalSquare_transportIso_precomp_heq p
    (s.precomp (snd (vertexFiber p a) P)) (fst (vertexFiber p a) P) (lift f (𝟙 P))
  exact h.trans (transportIntervalSquare_transportIso_heq_of_eq p _ _ _ _
    (transportIntervalSquare_universalSource_reindex p s f) (lift_fst f (𝟙 P)))

end SerrePositivity.InfinityCategories.F2
