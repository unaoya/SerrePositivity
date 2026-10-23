module
public import SerrePositivity.InfinityCategories.Stable.ExcisionSuspensionCornerRestriction

/-!
概要：四つの実 suspension 面の引き戻し性から、元の押し出しの像の普遍性を導く。
方針：全 cospan の厳密保存、同じ θ と対角合成、元の入力面の極限錐を接続する。
規約：標的の零対象や一般安定性は仮定しない。使われ方：一般切除・loop 同値判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

lemma excisionGridSuspensionFirstCospan_noninitial
    (v : ((horn 2 2 : SSet.{u}) ⊗ ((Δ[1] : SSet.{u}) ⊗ Δ[1])) _⦋0⦌) :
    IsExcisionFullPunctured (nerveEquiv
      ((cospanSquareBoundary ▷ ((Δ[1] : SSet.{u}) ⊗ Δ[1]) ≫
        excisionGridSuspensionShape).app (Opposite.op ⦋0⦌) v)) := by
  let w := cospanSquareBoundary.app (Opposite.op ⦋0⦌) v.1
  obtain ⟨i, hi⟩ := stdSimplex.obj₀Equiv.symm.surjective w.1
  obtain ⟨j, hj⟩ := stdSimplex.obj₀Equiv.symm.surjective w.2
  have hp := (nerveEquiv
    (excisionFullInputCospanBoundary.app (Opposite.op ⦋0⦌) v.1)).property
  have h := congrArg nerveEquiv (ConcreteCategory.congr_hom (NatTrans.congr_app
    excisionFullInputCospanBoundary_projection (Opposite.op ⦋0⦌)) v.1)
  change (nerveEquiv (excisionFullInputCospanBoundary.app (Opposite.op ⦋0⦌) v.1)).val =
    nerveEquiv (excisionGridSquareEmbedding.app (Opposite.op ⦋0⦌) w) at h
  rw [h] at hp
  have hab : i ≠ 0 ∨ j ≠ 0 := by
    by_cases h0 : i = 0
    · right
      intro h1
      have hw : w = (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 0) :=
        Prod.ext (hi.symm.trans (congrArg stdSimplex.obj₀Equiv.symm h0))
          (hj.symm.trans (congrArg stdSimplex.obj₀Equiv.symm h1))
      rw [hw] at hp
      change 1 ≤ 0 + 0 at hp
      omega
    · exact Or.inl h0
  have hv := excisionGridSuspensionEvaluateShape_noninitial i j hab v.2
  have hw : (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j) = w :=
    Prod.ext hi hj
  change IsExcisionFullPunctured (nerveEquiv
    (excisionGridSuspensionShape.app (Opposite.op ⦋0⦌) (w, v.2)))
  rw [← hw]
  exact hv

end SerrePositivity.InfinityCategories
