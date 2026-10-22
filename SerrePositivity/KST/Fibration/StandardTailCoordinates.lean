module
public import SerrePositivity.KST.Fibration.StandardJoinTailFace
public import SerrePositivity.KST.Fibration.WeakStringFiniteComparison
public import SerrePositivity.InfinityCategories.Core.OuterHornJoin

/-! # 元の貼り合わせの先行包含・最後の辺と標準的な添字の厳密照合 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 元の先行単体の包含は、元の最後の面射そのもの。 -/
lemma standardTailPrefix_inclusion (n : ℕ) :
    standardTailPrefix.{u} n ≫ standardTailInclusion n =
      stdSimplex.δ (Fin.last (n + 2)) := by
  apply (cancel_epi (tailPrefixStdIso n).hom).1
  change (tailPrefixStdIso n).hom ≫
    (((tailPrefixStdIso n).inv ≫ tailAttachmentPrefix Δ[n]) ≫
      ((tailAttachment (Δ[n] : SSet.{u})).ι ≫ (joinStdSimplexIso n 1).hom)) = _
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  change joinUnionRight (⊥ : (Δ[n] : SSet.{u}).Subcomplex) (horn 1 0) ≫
    (joinUnion (⊥ : (Δ[n] : SSet.{u}).Subcomplex) (horn 1 0)).ι ≫ _ = _
  rw [← Category.assoc, joinUnionRight_ι]
  change _ = (joinMap (𝟙 _) initialHornPointIso.inv ≫ (joinStdSimplexIso n 0).hom) ≫ _
  rw [Category.assoc, ← standardJoin_right_initial_face, ← Category.assoc, ← joinMap_comp]
  have he : initialHornPointIso.{u}.inv ≫ stdSimplex.δ (1 : Fin 2) = (horn 1 0).ι := by
    rw [← initialHornPointIso_ι, Iso.inv_hom_id_assoc]
  rw [Category.id_comp, he]

/-- 元の最後の実辺は、既存の連続辺の終端添字そのもの。 -/
lemma standardTailEdge_eq_consecutive (n : ℕ) :
    tailAttachmentEdge (Δ[n] : SSet.{u}) ≫ standardTailInclusion n =
      stdSimplex.map (consecutiveWeakStringEdge (n + 2) (Fin.last (n + 1))) := by
  rw [standardTailEdge_inclusion]
  apply SSet.yonedaEquiv.injective
  rw [InfinityCategories.joinStdSimplexIso_inr_edge]
  apply stdSimplex.ext
  intro a
  fin_cases a <;> rfl

end SerrePositivity.KST.Fibration
