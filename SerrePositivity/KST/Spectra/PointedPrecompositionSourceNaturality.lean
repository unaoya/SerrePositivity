module

public import SerrePositivity.KST.Spectra.PointedPrecompositionNaturality
public import SerrePositivity.KST.Spectra.PointedRelativeTransposeHomotopy

/-!
概要：源区間の標的へ後合成する操作と、その区間を前合成へ移す操作の厳密な交換。
方針：転置した普遍評価の前合成座標を使う。
規約：区間の再選択なし。使われ方：射影固定の切断比較から自然性正方形の定数辺を得る。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.PointedMapping

/-- 源区間の標的への後合成は、前合成作用の入力への同じ制限となる。 -/
lemma preAction_post_input {W D D' E : PointedSimplicialSet.{u}} (p : D ⟶ D') :
    PointedObject.basedHomMap W p ≫ preAction W D' E =
      preAction W D E ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed p E) (PointedObject.basedHom W E) := by
  rw [preAction_restrict]
  have ht := congrArg transpose (transpose_evaluation_pre p E)
  rw [transpose_transpose] at ht
  unfold preAction
  change (ihom W).map p ≫
      ((ihom W).map (transpose (𝟙 (PointedObject.basedHom D' E))) ≫ _) = _
  rw [← Category.assoc, ← Functor.map_comp, ht]
  rfl

/-- 同じ源区間への後合成と前合成移送は、実辺全体で厳密に可換。 -/
lemma VerticalPath.basedPre_post_input_path {W D D' E : PointedSimplicialSet.{u}}
    {a b : W ⟶ D} (H : VerticalPath (PointedObject.toPoint D) a b) (p : D ⟶ D') :
    ((H.basedPost p).basedPre E).path = ((H.basedPre E).pre (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed p E)).path := by
  rw [VerticalPath.basedPre_action_path]
  change (H.path ≫ (PointedObject.basedHomMap W p).right) ≫ _ = (H.basedPre E).path ≫ _
  rw [VerticalPath.basedPre_action_path]
  simpa only [Under.comp_right, Category.assoc] using
    congrArg (fun q => H.path ≫ q.right) (preAction_post_input (W := W) (E := E) p)

end SerrePositivity.KST.Spectra.PointedMapping
