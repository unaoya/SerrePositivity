module
public import SerrePositivity.InfinityCategories.Derived.DGModuleInputAugmentationSquare
public import SerrePositivity.InfinityCategories.Derived.FunctorHomotopyStrictBasePrecomp
/-!
概要：指定実入力比較の augmentation 正方形を、元の入力 nerve で制限する。
方針：基底上の指定恒等を元の入力 Up でも保ち、同じ交換正方形を適用する。
規約：元の指定比較の値を保持する。使われ方：元の resolved augmentation 正方形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet MonoidalCategory
open scoped Simplicial
variable (R : Type u) [CommRing R] (A C : Type (max (u + 1) v))
  [DGCategory R A] [DGCategory R C]
  (E : Type v) [DGCategory R E] [Small.{u} E]
  (H : DGFunctor R A C) (F : DGFunctor R C (RightModule R E))
/-- 同じ入力 Up で制限した指定実入力比較は、元の augmentation の全関手正方形を保つ。 -/
lemma dgModuleResolutionPrecompSourceIso_inputUp_augmentation_heq :
    let a := dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R A)
    HEq ((((dgModuleResolutionPrecompSourceIso R A C E H F).precomp a).postcomp
        (dgNerve.map (dgModuleAugmentationSource R C E F))).hom ≫
      (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (functorHomotopyPrecomp (dgModuleAugmentationInputBaseHomotopy R C E F)
          (a ≫ (dgNerve.map ((dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R A).comp
            (H.comp (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C))) ≫
              (dgModuleFunctorResolutionSourceNerveEquivalence R C E F).inv))))))
      (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (functorHomotopyPrecomp (dgModuleAugmentationInputBaseHomotopy R C E F)
          (a ≫ ((dgModuleFunctorResolutionSourceNerveEquivalence R A E (H.comp F)).inv ≫
            dgNerve.map (dgModuleResolutionPrecompFunctor R A C E H F)))))) := by
  extract_lets a
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
  exact strictBaseHomotopySquare_precomp_heq
    (dgModuleResolutionPrecompSourceIso R A C E H F) p
    (dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R C) ≫ dgNerve.map F)
    (dgNerve.map (dgModuleAugmentationSource R C E F))
    (dgModuleAugmentationInputBaseHomotopy R C E F) h hf hg he a
end SerrePositivity.InfinityCategories
