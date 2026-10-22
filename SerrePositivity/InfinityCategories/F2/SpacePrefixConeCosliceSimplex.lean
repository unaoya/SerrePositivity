module

public import SerrePositivity.InfinityCategories.F2.CoherentPrefixConeSimplex
public import SerrePositivity.InfinityCategories.F2.SpaceCosliceEdgeComponent

/-!
概要：prefix 変形の実単体を固定初点の coslice に入れる。
方針：join の標準同型を使い、同じ始点条件と全座標を保持する。
規約：元の全 cone と時刻に依存し、代表を選び直さない。
使われ方：零面の全族比較を指定円柱で表示する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 固定始点を保持した prefix 変形の実 coslice 単体。 -/
def spacePrefixConeCosliceSimplex {m n : ℕ} (s : SpaceInfinity.{u} _⦋n + 1⦌)
    (a : Fin (m + 1) →o Fin (n + 1)) (t : Fin (m + 1) →o Fin 2) :
    (sliceUnder (SSet.yonedaEquiv.symm
      (coherentNerveVertex (s.obj ⟨ULift.up 0⟩)))) _⦋m⦌ := by
  refine ⟨(leftPointStdSimplexIso m).hom ≫
    SSet.yonedaEquiv.symm (coherentPrefixConeSimplex s a t), ?_⟩
  rw [← Category.assoc, joinStdSimplexIso_leftPoint_inl,
    SSet.yonedaEquiv_symm_naturality_left]
  congr 1
  apply (coherentNerveVertexEquiv KanObject).symm.injective
  rfl

/-- 実 coslice 単体の座標は同じ元の prefix 変形そのもの。 -/
lemma spacePrefixConeCosliceSimplex_coordinates {m n : ℕ}
    (s : SpaceInfinity.{u} _⦋n + 1⦌)
    (a : Fin (m + 1) →o Fin (n + 1)) (t : Fin (m + 1) →o Fin 2) :
    coherentCosliceSourceSimplex (s.obj ⟨ULift.up 0⟩)
      (spacePrefixConeCosliceSimplex s a t) = coherentPrefixConeSimplex s a t := by
  change SSet.yonedaEquiv ((leftPointStdSimplexIso m).inv ≫
    ((leftPointStdSimplexIso m).hom ≫
      SSet.yonedaEquiv.symm (coherentPrefixConeSimplex s a t))) = _
  rw [Iso.inv_hom_id_assoc, Equiv.apply_symm_apply]

/-- 実 coslice 単体は tail と時刻の同時制限と厳密に可換。 -/
lemma spacePrefixConeCosliceSimplex_reindex {m n k : ℕ}
    (s : SpaceInfinity.{u} _⦋n + 1⦌)
    (a : Fin (m + 1) →o Fin (n + 1)) (t : Fin (m + 1) →o Fin 2)
    (r : ⦋k⦌ ⟶ ⦋m⦌) :
    (sliceUnder (SSet.yonedaEquiv.symm (coherentNerveVertex (s.obj ⟨ULift.up 0⟩)))).map
      r.op (spacePrefixConeCosliceSimplex s a t) =
        spacePrefixConeCosliceSimplex s (a.comp r.toOrderHom) (t.comp r.toOrderHom) := by
  apply spaceCosliceSourceSimplex_injective (s.obj ⟨ULift.up 0⟩) k
  exact (coherentCosliceSourceSimplex_reindex _ r _).symm.trans
    ((congrArg (fun z ↦ (SimplicialThickening.functor
      (prependOrderHom r.toOrderHom).uliftMap).comp SSet z)
        (spacePrefixConeCosliceSimplex_coordinates s a t)).trans
      ((coherentPrefixConeSimplex_reindex s a t r.toOrderHom).trans
        (spacePrefixConeCosliceSimplex_coordinates s _ _).symm))

end SerrePositivity.InfinityCategories.F2
