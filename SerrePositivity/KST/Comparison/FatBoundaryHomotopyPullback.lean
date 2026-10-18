module

public import SerrePositivity.KST.Comparison.FatSkeletonRowRelations
public import SerrePositivity.KST.Comparison.BoundaryFaceRepresentation
public import SerrePositivity.KST.Comparison.TensorBoundaryGluing
public import SerrePositivity.KST.Comparison.TensorRestriction
public import SerrePositivity.KST.Comparison.TensorHomotopyPullbacks
public import SerrePositivity.KST.Comparison.HomotopyPullbackPasting

/-!
# 低い行から境界の付着のホモトピー引き戻しへ

概要：各低次元の行の骨格への比較から、新しい行の境界の比較を得る。
方針：面の標準単体表示と面の自然性の比較を貼り合わせ、境界を有限被覆で復元する。
規約：Segal 1974 Proposition 1.6 の帰納段階。各行の射の Kan 性を仮定する。
使われ方：有限骨格の付着の span への Lemma 1.7 の適用。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite MonoidalCategory
open scoped Simplicial

/--
概要：低い行の比較と面の比較から、境界の付着の四角形を得る。
方針：各非空な適切な面で二つの比較を横に貼り、境界の有限被覆に適用する。
規約：仮定は各行と各面の比較であり、境界全体の比較は仮定しない。
使われ方：Segal Proposition 1.6 の有限骨格の帰納。
-/
theorem fatBoundaryAttachment_homotopyPullback
    {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (α : F ⟶ G) (n : ℕ)
    (hKan : ∀ m, SSet.modelCategoryQuillen.J.rlp (α.app (op ⦋m⦌)))
    (hface : ∀ (m k : ℕ) (θ : ⦋m⦌ ⟶ ⦋k⦌), Function.Injective θ →
      IsHomotopyPullback (CommSq.mk (α.naturality θ.op)))
    (hrow : ∀ (m : ℕ) (hm : m ≤ n), IsHomotopyPullback
      (CommSq.mk (fatSkeletonRowOfLE_map α hm))) :
    IsHomotopyPullback (CommSq.mk (fatBoundaryAttachment_map α n)) := by
  let sq := CommSq.mk (fatBoundaryAttachment_map α n)
  apply tensorBoundary_homotopyPullback_of_faces sq
  intro S hS hproper
  obtain ⟨m, hm, θ, hθ, e, he⟩ := boundaryVertexFace_representation.{u} S hS hproper
  have hm' : m ≤ n := by omega
  let t := e.hom ≫ (boundaryVertexFace (n + 1) S).ι
  have ht : t ≫ (SSet.boundary (n + 1)).ι = SSet.stdSimplex.map θ := by
    simpa only [t, Category.assoc] using he
  have hθ' : Function.Injective θ := SimplexCategory.mono_iff_injective.mp hθ
  let sf := CommSq.mk (α.naturality θ.op)
  have hs := isHomotopyPullback_tensorRight sf (hface m (n + 1) θ hθ') Δ[m]
  let sr := CommSq.mk (fatSkeletonRowOfLE_map α hm')
  have hp := isHomotopyPullback_paste_horiz_of_middle_fibration
    ((tensorRight Δ[m]).map_commSq sf) sr hs (hrow m hm')
    (tensorRight_rlp _ (hKan m) Δ[m])
  apply (tensorRestriction_homotopyPullback_iff
    (tensorSubcomplexSquare sq (boundaryVertexFace (n + 1) S)) e.hom).mp
  have hF := fatBoundaryAttachment_face F hm' θ hθ' t ht
  have hG := fatBoundaryAttachment_face G hm' θ hθ' t ht
  apply (isHomotopyPullback_iff_of_localized_isIso
    (tensorRestrictionSquare (tensorSubcomplexSquare sq (boundaryVertexFace (n + 1) S)) e.hom)
    (((tensorRight Δ[m]).map_commSq sf).horiz_comp sr)
    (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _) ?_ (by simp) (by simp) ?_
    (by infer_instance) (by infer_instance) (by infer_instance) (by infer_instance)).mpr hp
  · simp only [Category.comp_id, Category.id_comp]
    rw [← whiskerLeft_comp_assoc]
    exact hF
  · simp only [Category.comp_id, Category.id_comp]
    rw [← whiskerLeft_comp_assoc]
    exact hG

end SerrePositivity.KST.Comparison
