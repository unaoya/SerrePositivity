module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseFaceImages
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.JoinPullback

/-!
概要：二つの境界面の交わりを共通の低次元の重みで表す pullback。
方針：標準単体の二面の pullback を頂点の欠落から直接構成し、反転と join で移す。
規約：全体の次元が二以上の場合を扱う。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、境界面から運んだ図式の重なりでの一致。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 概要：異なる二面の標準単体の包含は共通の低次元の面を pullback に持つ。
方針：二つの像が等しければ一方の単体の頂点は対応する番号を避け、面で一意に因数分解する。
規約：i≤j に対して外側の二面は i.castSucc と j.succ。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、境界の二面の接合の基本正方形。 -/
lemma stdSimplex_faces_isPullback {n : ℕ} (i j : Fin (n + 2)) (hij : i ≤ j) :
    IsPullback (stdSimplex.{u}.δ j) (stdSimplex.δ i)
      (stdSimplex.δ i.castSucc) (stdSimplex.δ j.succ) := by
  have hw : (stdSimplex.{u}.δ j) ≫ stdSimplex.δ i.castSucc =
      stdSimplex.δ i ≫ stdSimplex.δ j.succ := by
    change stdSimplex.map (SimplexCategory.δ j) ≫ stdSimplex.map (SimplexCategory.δ i.castSucc) =
      stdSimplex.map (SimplexCategory.δ i) ≫ stdSimplex.map (SimplexCategory.δ j.succ)
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      SimplexCategory.δ_comp_δ hij]
  apply IsPullback.of_forall_isPullback_app
  rintro ⟨⟨d⟩⟩
  let k := Opposite.op ⦋d⦌
  apply (Types.isPullback_iff _ _ _ _).2
  refine ⟨NatTrans.congr_app hw k, ?_, ?_⟩
  · intro x y h
    exact (mono_iff_injective ((stdSimplex.{u}.δ j).app k)).mp inferInstance h.1
  · intro x y h
    have hmiss : ∀ a : Fin (d + 1), x a ≠ j := by
      intro a ha
      have hv := congrArg (fun z : (Δ[n + 2] : SSet.{u}) _⦋d⦌ ↦ z a) h
      change i.castSucc.succAbove (x a) = j.succ.succAbove (y a) at hv
      rw [ha, Fin.succAbove_of_le_castSucc _ _ (by exact hij)] at hv
      exact Fin.succAbove_ne j.succ (y a) hv.symm
    let f := SimplexCategory.factor_δ (stdSimplex.objEquiv x) j
    let z : (Δ[n] : SSet.{u}) _⦋d⦌ := stdSimplex.objEquiv.symm f
    have hz : (stdSimplex.δ j).app k z = x := by
      change stdSimplex.objEquiv.symm (f ≫ SimplexCategory.δ j) = x
      rw [SimplexCategory.factor_δ_spec _ _ hmiss, Equiv.symm_apply_apply]
    refine ⟨z, hz, ?_⟩
    apply (mono_iff_injective ((stdSimplex.{u}.δ j.succ).app k)).mp inferInstance
    have he := ConcreteCategory.congr_hom (NatTrans.congr_app hw k) z
    change (stdSimplex.δ i.castSucc).app k ((stdSimplex.δ j).app k z) =
      (stdSimplex.δ j.succ).app k ((stdSimplex.δ i).app k z) at he
    rw [hz] at he
    exact he.symm.trans h

/-- 概要：edgewise の境界の二面の重みの正方形は pullback。
方針：標準単体の二面の pullback の反転と元の正方形の join を取る。
規約：i≤j に対応する全体の面は i.castSucc と j.succ。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、同じ重みの単体を二面から表示した際の共通表示。 -/
lemma edgewiseWeight_faces_isPullback {n : ℕ} (i j : Fin (n + 2)) (hij : i ≤ j) :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.{u}.map (SimplexCategory.δ j))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ i))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ i.castSucc))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ j.succ)) := by
  letI : SSet.opFunctor.{u}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor
  have h := stdSimplex_faces_isPullback.{u} i j hij
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.join_isPullback (h.map SSet.opFunctor) h

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
