module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionInputComparison
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationInputBaseHomotopy
public import SerrePositivity.InfinityCategories.Derived.FunctorHomotopyStrictBaseSquare
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationPrecompPrism
/-!
概要：元の指定実入力比較と実 augmentation の全関手射の正方形を照合する。
方針：基底像の指定恒等を相殺し、全円柱の入力自然性で元の前合成 augmentation を回収する。
規約：生の augmentation の可逆性は不要。使われ方：元の分解関手の raw factor 正方形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet MonoidalCategory
open scoped Simplicial
private lemma refl_heq_of_map_eq {X Y : SSet.{u}} {f g : X ⟶ Y} (h : f = g) :
    HEq (Iso.refl (HomotopyCategory.mk (functorVertex f)))
      (Iso.refl (HomotopyCategory.mk (functorVertex g))) := by cases h; rfl
variable (R : Type u) [CommRing R] (A C : Type (max (u + 1) v))
  [DGCategory R A] [DGCategory R C]
  (E : Type v) [DGCategory R E] [Small.{u} E]
  (H : DGFunctor R A C) (F : DGFunctor R C (RightModule R E))
/-- 指定実入力比較と、実入力射影を終点とする同じ augmentation の交換正方形。 -/
lemma dgModuleResolutionPrecompSourceIso_inputBase_augmentation_heq :
    HEq (((dgModuleResolutionPrecompSourceIso R A C E H F).postcomp
        (dgNerve.map (dgModuleAugmentationSource R C E F))).hom ≫
      (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (functorHomotopyPrecomp (dgModuleAugmentationInputBaseHomotopy R C E F)
          (dgNerve.map ((dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R A).comp
            (H.comp (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C))) ≫
              (dgModuleFunctorResolutionSourceNerveEquivalence R C E F).inv)))))
      (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (functorHomotopyPrecomp (dgModuleAugmentationInputBaseHomotopy R C E F)
          ((dgModuleFunctorResolutionSourceNerveEquivalence R A E (H.comp F)).inv ≫
            dgNerve.map (dgModuleResolutionPrecompFunctor R A C E H F))))) := by
  let Q := dgModuleFunctorResolutionSourceNerveEquivalence R A E (H.comp F)
  let S := dgModuleFunctorResolutionSourceNerveEquivalence R C E F
  let J := dgNerve.map (dgModuleResolutionPrecompFunctor R A C E H F)
  let h := dgNerve.map ((dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R A).comp
    (H.comp (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C)))
  let p := dgNerve.map (dgModuleFunctorResolutionSourceLift R C E F)
  have hs : J ≫ S.hom = Q.hom ≫ h := by
    have hs := congrArg (fun G => dgNerve.map G)
      (dgModuleResolutionPrecompFunctor_sourceLift R A C E H F)
    simpa only [dgNerve.map_comp] using! hs
  have hQ : Q.inv ≫ Q.hom = 𝟙 _ :=
    dgModuleFunctorResolutionSourceNerveEquivalence_inv_hom R A E (H.comp F)
  have hS : S.inv ≫ S.hom = 𝟙 _ :=
    dgModuleFunctorResolutionSourceNerveEquivalence_inv_hom R C E F
  have hf : (Q.inv ≫ J) ≫ p = h := by
    change (Q.inv ≫ J) ≫ S.hom = h
    rw [Category.assoc, hs, ← Category.assoc, hQ, Category.id_comp]
  have hg : (h ≫ S.inv) ≫ p = h := by
    change (h ≫ S.inv) ≫ S.hom = h
    rw [Category.assoc, hS, Category.comp_id]
  have he := dgModuleResolutionPrecompSourceIso_postcomp_source_heq R A C E H F
  have he' : HEq ((dgModuleResolutionPrecompSourceIso R A C E H F).postcomp p)
      (Iso.refl (HomotopyCategory.mk (functorVertex ((Q.inv ≫ J) ≫ p)))) :=
    he.trans (refl_heq_of_map_eq hf.symm)
  exact strictBaseHomotopySquare_heq (dgModuleResolutionPrecompSourceIso R A C E H F)
    p (dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R C) ≫ dgNerve.map F)
    (dgNerve.map (dgModuleAugmentationSource R C E F))
    (dgModuleAugmentationInputBaseHomotopy R C E F) (hg.trans hf.symm) he'

/-- 指定実入力比較の後続像と元の augmentation は、前合成後の同じ全関手射を回収する。 -/
lemma dgModuleResolutionPrecompSourceIso_augmentation_heq :
    HEq (((dgModuleResolutionPrecompSourceIso R A C E H F).postcomp
        (dgNerve.map (dgModuleAugmentationSource R C E F))).hom ≫
      (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (functorHomotopyPrecomp (dgModuleAugmentationInputBaseHomotopy R C E F)
          (dgNerve.map ((dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R A).comp
            (H.comp (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C))) ≫
              (dgModuleFunctorResolutionSourceNerveEquivalence R C E F).inv)))))
      (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (functorHomotopyPrecomp (dgModuleAugmentationUnliftedHomotopy R A E (H.comp F))
          (dgModuleFunctorResolutionSourceNerveEquivalence R A E (H.comp F)).inv))) := by
  let Q := dgModuleFunctorResolutionSourceNerveEquivalence R A E (H.comp F)
  let J := dgNerve.map (dgModuleResolutionPrecompFunctor R A C E H F)
  have hb := dgModuleResolutionPrecompSourceIso_inputBase_augmentation_heq R A C E H F
  have hraw : (functorHomotopyPrecomp
      (dgModuleAugmentationInputBaseHomotopy R C E F) (Q.inv ≫ J)).h =
      (functorHomotopyPrecomp
        (dgModuleAugmentationUnliftedHomotopy R A E (H.comp F)) Q.inv).h := by
    change ((Q.inv ≫ J) ▷ (Δ[1] : SSet)) ≫
      (dgModuleAugmentationUnliftedHomotopy R C E F).h =
        (Q.inv ▷ (Δ[1] : SSet)) ≫
          (dgModuleAugmentationUnliftedHomotopy R A E (H.comp F)).h
    rw [comp_whiskerRight, Category.assoc,
      dgModuleAugmentationUnliftedHomotopy_precomp R A C E H F]
  exact hb.trans (functorHomotopyHom_heq_of_raw_eq _ _ hraw)
end SerrePositivity.InfinityCategories
