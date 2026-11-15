module

public import SerrePositivity.InfinityCategories.Sheaves.SiteAsSmallEquivalence

/-!
概要：元の大きい site の全被覆篩の層条件と、小さい模型の元の層条件を比較する。
方針：同じ AsSmall 表示の site 同値へ移し、検証済みの元の全制限錐の比較を用いる。
使われ方：HTT 6.2.2.6、Kerodon §4.5.1（Tag 01DQ）の本質的小さい site の層。
規約：対象 Type(u+1)・射 Type u・係数 SSet(u+1)。EssentiallySmall 以外の濃度条件なし。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Functor SSet
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type (u + 1)} [Category.{u} C] {D : Type u} [SmallCategory D]
variable {E : SSet.{u + 1}} [Quasicategory E]

/-- 小さい模型の同じ全単体の射は、AsSmall 表示を通る元の全射と厳密に一致する。 -/
lemma siteSmallModelShapeEquivalence_asSmall (e : D ≌ C) :
    (asSmallSiteShapeIso D).hom ≫ nerveMap (siteAsSmallEquivalence e).functor.op ≫
      (largeSiteShapeIso C).inv = (siteSmallModelShapeEquivalence e).hom := rfl

/-- 元の全被覆篩の大きい site の層条件を、同じ係数の小さい模型へ保存・反映する。 -/
theorem largeIsSheaf_smallModel_iff (e : D ≌ C)
    (J : GrothendieckTopology D) (K : GrothendieckTopology C)
    (hf : CoverPreserving J K e.functor) (hg : CoverPreserving K J e.inverse)
    (F : nerve Cᵒᵖ ⟶ E) :
    IsSheaf J ((siteSmallModelShapeEquivalence e).hom ≫ F) ↔ LargeIsSheaf K F := by
  let a := siteAsSmallEquivalence e
  let JA := (AsSmall.down : AsSmall.{u + 1} D ⥤ D).inducedTopology J
  let KA := (AsSmall.down : AsSmall.{u + 1} C ⥤ C).inducedTopology K
  let O := asSmallLargePresheaf F
  let O' := nerveMap a.functor.op ≫ O
  have hfA : CoverPreserving JA KA a.functor :=
    siteAsSmallEquivalence_coverPreserving e J K hf
  have hgA : CoverPreserving KA JA a.inverse :=
    siteAsSmallEquivalence_coverPreserving e.symm K J hg
  have h := (isSheaf_asSmall_inducedTopology_iff J O').trans
    (nativeIsSheaf_reindex_equivalence_iff a JA KA hfA hgA O)
  have he : (asSmallSiteShapeIso D).hom ≫ O' =
      (siteSmallModelShapeEquivalence e).hom ≫ F := by
    change ((asSmallSiteShapeIso D).hom ≫ nerveMap (siteAsSmallEquivalence e).functor.op ≫
      (largeSiteShapeIso C).inv) ≫ F = _
    rw [siteSmallModelShapeEquivalence_asSmall]
  rw [he] at h
  exact h

/-- 元の EssentiallySmall 入力だけから、元の小さい模型と大きい site の層条件を比較する。 -/
theorem largeIsSheaf_essentiallySmall_iff [EssentiallySmall.{u} C]
    (J : GrothendieckTopology C) (F : nerve Cᵒᵖ ⟶ E) :
    IsSheaf ((equivSmallModel.{u} C).inverse.inducedTopology J)
      ((essentiallySmallSiteShapeEquivalence C).hom ≫ F) ↔ LargeIsSheaf J F := by
  let e : SmallModel.{u} C ≌ C := (equivSmallModel.{u} C).symm
  letI : (equivSmallModel.{u} C).functor.IsDenseSubsite J
      ((equivSmallModel.{u} C).inverse.inducedTopology J) := by infer_instance
  apply largeIsSheaf_smallModel_iff e
  · exact CoverPreserving.of_isContinuous (F := e.functor)
      (e.functor.inducedTopology J) J
  · exact Functor.IsDenseSubsite.coverPreserving J
      ((equivSmallModel.{u} C).inverse.inducedTopology J) (equivSmallModel.{u} C).functor

end SerrePositivity.InfinityCategories.Sheaves
