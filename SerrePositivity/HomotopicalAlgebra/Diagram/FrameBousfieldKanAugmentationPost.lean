module

public import SerrePositivity.HomotopicalAlgebra.Diagram.FrameWeightPostcomposition
public import SerrePositivity.HomotopicalAlgebra.Diagram.FrameBousfieldKanAugmentation

/-!
概要：左随伴とframe実現の交換同型は、元のBK増大射を保つ。
方針：指定随伴のHom同値で転置し、零単体のYonedaと随伴単位の自然性を使う。
使われ方：HTT 4.2.4.4、RR02(a)の評価と実現の交換の照合。
規約：既存のpostIsoと元の余錐の脚を保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w u v
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.DiagramModel.FrameWeightRealization
variable (K : Type w) [SmallCategory K]
  {C : Type u} [Category.{w} C] [HasColimitsOfSize.{w, w} C]
  {D : Type v} [Category.{w} D] [HasColimitsOfSize.{w, w} D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (A : K ⥤ SimplexCategory ⥤ C)
  (c : Cocone (ConstantWeightHom.degree K A (SimplexCategory.mk 0)))

/-- 元の次数零余錐の脚を、同じ左随伴で送る。 -/
def postZeroCocone :
    Cocone (ConstantWeightHom.degree K (postFrames K A L) (SimplexCategory.mk 0)) where
  pt := L.obj c.pt
  ι := {
    app k := L.map (c.ι.app k)
    naturality k l f := by
      change L.map ((A.map f).app (SimplexCategory.mk 0)) ≫ L.map (c.ι.app l) =
        L.map (c.ι.app k) ≫ 𝟙 _
      rw [← L.map_comp]
      have h := c.ι.naturality f
      change (A.map f).app (SimplexCategory.mk 0) ≫ c.ι.app l = c.ι.app k ≫ 𝟙 _ at h
      rw [h, Category.comp_id, Category.comp_id] }

lemma zeroWeightCocone_post :
    (ConstantWeightHom.homEquiv K (postFrames K A L) (SimplexCategory.mk 0)
        (L.obj c.pt)).symm (postZeroCocone K A c (L := L)).ι ≫
      (homPostIso K adj A).hom.app (L.obj c.pt) =
    (ConstantWeightHom.homEquiv K A (SimplexCategory.mk 0) c.pt).symm c.ι ≫
      (hom K A).map (adj.unit.app c.pt) := by
  apply (ConstantWeightHom.homEquiv K A (SimplexCategory.mk 0) (R.obj (L.obj c.pt))).injective
  rw [ConstantWeightHom.homEquiv_target_naturality, Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext k
  change SSet.yonedaEquiv (SSet.yonedaEquiv.symm (L.map (c.ι.app k)) ≫
      ((homPostIso K adj A).hom.app (L.obj c.pt)).app (Opposite.op k)) =
    c.ι.app k ≫ adj.unit.app c.pt
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  let g : (A.obj k).obj (SimplexCategory.mk 0) ⟶ c.pt := c.ι.app k
  change adj.homEquiv _ (L.obj c.pt) (L.map g) = g ≫ adj.unit.app c.pt
  simpa only [Category.comp_id, Adjunction.homEquiv_id] using
    adj.homEquiv_naturality_left g (𝟙 (L.obj c.pt))

lemma postIso_augmentation :
    (postIso K adj A).hom.app (bousfieldKanWeight Kᵒᵖ) ≫
        bousfieldKanAugmentation (postFrames K A L) (postZeroCocone K A c (L := L)) =
      L.map (bousfieldKanAugmentation A c) := by
  have h : adj.homEquiv _ _ (L.map (bousfieldKanAugmentation A c)) =
      bousfieldKanAugmentation A c ≫ adj.unit.app c.pt := by
    simpa only [Category.comp_id, Adjunction.homEquiv_id] using
      adj.homEquiv_naturality_left (bousfieldKanAugmentation A c) (𝟙 (L.obj c.pt))
  apply (((adjunction K A).comp adj).homEquiv _ _).injective
  rw [postIso_homEquiv, bousfieldKanAugmentation_homEquiv, Category.assoc]
  change bousfieldKanZeroWeight K ≫
    ((ConstantWeightHom.homEquiv K (postFrames K A L) (SimplexCategory.mk 0)
      (L.obj c.pt)).symm (postZeroCocone K A c (L := L)).ι ≫
      (homPostIso K adj A).hom.app (L.obj c.pt)) =
    (((adjunction K A).comp adj).homEquiv _ (L.obj c.pt)) (L.map (bousfieldKanAugmentation A c))
  rw [zeroWeightCocone_post, Adjunction.comp_homEquiv]
  change _ = (adjunction K A).homEquiv _ (R.obj (L.obj c.pt))
    (adj.homEquiv _ (L.obj c.pt) (L.map (bousfieldKanAugmentation A c)))
  rw [h, Adjunction.homEquiv_naturality_right, bousfieldKanAugmentation_homEquiv,
    Category.assoc]

end SerrePositivity.DiagramModel.FrameWeightRealization
