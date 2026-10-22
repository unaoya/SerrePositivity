module

public import SerrePositivity.InfinityCategories.F2.CoherentPrefixMaximalAbsorption
public import SerrePositivity.InfinityCategories.F2.CoherentPrefixConeTail

/-!
概要：最大 path の図式を標的とする prefix 変形は元の通常の制限。
方針：最大化の吸収式と添字変換を使う。
規約：全ての tail 単体と時刻の作用を保持する。
使われ方：元の図式を固定する比較円柱の射影。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 最大化した単体では任意の prefix 変形が同じ通常の制限に等しい。 -/
lemma coherentSimplexMaximalization_prefix_invariant
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {m n : ℕ}
    (s : (SimplicialNerve C) _⦋n⦌)
    (a : ULift.{u} (Fin (m + 1)) →o ULift.{u} (Fin (n + 1)))
    (t : ULift.{u} (Fin (m + 1)) →o Fin 2) :
    (coherentPrefixPathDeformationEnriched a t).comp SSet (coherentSimplexMaximalization s) =
      (SimplicialThickening.functor a).comp SSet (coherentSimplexMaximalization s) := by
  change ((coherentPrefixPathDeformationEnriched a t).comp SSet
    (coherentPathDeformationEnriched OrderHom.id (OrderHom.const _ 1))).comp SSet s = _
  rw [coherentPrefixPathDeformationEnriched_maximal_absorption]
  exact congrArg (fun F ↦ F.comp SSet s)
    (coherentPathDeformationEnriched_reindex a OrderHom.id (OrderHom.const _ 1)).symm

/-- 元の tail が最大化表示なら cone の prefix 変形はその図式を固定する。 -/
lemma coherentPrefixConeSimplex_tail_of_maximal
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {m n : ℕ}
    (s : (SimplicialNerve C) _⦋n + 1⦌) (r : (SimplicialNerve C) _⦋n⦌)
    (hr : (SimplicialNerve C).δ 0 s = coherentSimplexMaximalization r)
    (a : Fin (m + 1) →o Fin (n + 1)) (t : Fin (m + 1) →o Fin 2) :
    (SimplicialNerve C).δ 0 (coherentPrefixConeSimplex s a t) =
      (SimplicialThickening.functor a.uliftMap).comp SSet (coherentSimplexMaximalization r) := by
  have h := coherentPrefixConeSimplex_tail s a t
  rw [hr] at h
  exact h.trans (coherentSimplexMaximalization_prefix_invariant r _ _)

end SerrePositivity.InfinityCategories.F2
