module
public import SerrePositivity.KST.Fibration.StandardJoinTailFace
public import SerrePositivity.KST.Fibration.WeakStringFiniteComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.OuterHornJoin

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
      ((tailAttachment (Δ[n] : SSet.{u})).ι ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 1).hom)) = _
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionRight (⊥ : (Δ[n] : SSet.{u}).Subcomplex) (horn 1 0) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion (⊥ : (Δ[n] : SSet.{u}).Subcomplex) (horn 1 0)).ι ≫ _ = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionRight_ι]
  change _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) initialHornPointIso.inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom) ≫ _
  rw [Category.assoc, ← standardJoin_right_initial_face, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp]
  have he : initialHornPointIso.{u}.inv ≫ stdSimplex.δ (1 : Fin 2) = (horn 1 0).ι := by
    rw [← initialHornPointIso_ι, Iso.inv_hom_id_assoc]
  rw [Category.id_comp, he]

/-- 元の最後の実辺は、既存の連続辺の終端添字そのもの。 -/
lemma standardTailEdge_eq_consecutive (n : ℕ) :
    tailAttachmentEdge (Δ[n] : SSet.{u}) ≫ standardTailInclusion n =
      stdSimplex.map (consecutiveWeakStringEdge (n + 2) (Fin.last (n + 1))) := by
  rw [standardTailEdge_inclusion]
  apply SSet.yonedaEquiv.injective
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.joinStdSimplexIso_inr_edge]
  apply stdSimplex.ext
  intro a
  fin_cases a <;> rfl

end SerrePositivity.KST.Fibration
