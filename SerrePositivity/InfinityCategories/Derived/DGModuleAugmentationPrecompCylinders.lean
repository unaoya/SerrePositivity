module
public import SerrePositivity.InfinityCategories.Derived.DGModuleInputAugmentationSquare
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedAugmentationHomotopy
public import SerrePositivity.InfinityCategories.Derived.DGUniverseLiftNervePrecomposition
/-!
概要：実入力 Up で制限した正方形の両円柱を、元の resolved augmentation の円柱へ同定する。
方針：同じ入力 Up の厳密等式と、全円柱の前合成自然性を使う。
規約：同じ実円柱射を保つ。使われ方：元の resolved precompIso の augmentation 正方形。
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
/-- 正方形の基底側の円柱は、元の resolved augmentation の入力 nerve による制限である。 -/
lemma dgModuleResolvedAugmentationHomotopy_precomp_inputBase_raw :
    (functorHomotopyPrecomp (dgModuleResolvedAugmentationHomotopy R C E F)
      (dgNerve.map H)).h =
    (functorHomotopyPrecomp (dgModuleAugmentationInputBaseHomotopy R C E F)
      (dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R A) ≫
        dgNerve.map ((dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R A).comp
          (H.comp (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C))) ≫
            (dgModuleFunctorResolutionSourceNerveEquivalence R C E F).inv)).h := by
  let S := dgModuleFunctorResolutionSourceNerveEquivalence R C E F
  let UA := dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R A)
  let UC := dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C)
  let h := dgNerve.map ((dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R A).comp
    (H.comp (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C)))
  let q := dgNerve.map H
  have hUp : UA ≫ h = q ≫ UC :=
    dgUniverseLift_sourcePrecomp_nerve.{u, v, v} R A C H
  have hm : q ≫ (UC ≫ S.inv) = UA ≫ h ≫ S.inv := by
    simpa only [Category.assoc] using congrArg (fun m => m ≫ S.inv) hUp.symm
  change (q ▷ (Δ[1] : SSet)) ≫ (((UC ≫ S.inv) ▷ (Δ[1] : SSet)) ≫
    (dgModuleAugmentationUnliftedHomotopy R C E F).h) =
      ((UA ≫ h ≫ S.inv) ▷ (Δ[1] : SSet)) ≫
        (dgModuleAugmentationUnliftedHomotopy R C E F).h
  simpa only [comp_whiskerRight, Category.assoc] using
    congrArg (fun m => (m ▷ (Δ[1] : SSet)) ≫
      (dgModuleAugmentationUnliftedHomotopy R C E F).h) hm
/-- 正方形の前合成側の円柱は、元の前合成関手の同じ resolved augmentation である。 -/
lemma dgModuleResolvedAugmentationHomotopy_precomp_source_raw :
    (dgModuleResolvedAugmentationHomotopy R A E (H.comp F)).h =
    (functorHomotopyPrecomp (dgModuleAugmentationInputBaseHomotopy R C E F)
      (dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R A) ≫
        (dgModuleFunctorResolutionSourceNerveEquivalence R A E (H.comp F)).inv ≫
          dgNerve.map (dgModuleResolutionPrecompFunctor R A C E H F))).h := by
  let Q := dgModuleFunctorResolutionSourceNerveEquivalence R A E (H.comp F)
  let UA := dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R A)
  let J := dgNerve.map (dgModuleResolutionPrecompFunctor R A C E H F)
  change ((UA ≫ Q.inv) ▷ (Δ[1] : SSet)) ≫
    (dgModuleAugmentationUnliftedHomotopy R A E (H.comp F)).h =
      ((UA ≫ Q.inv ≫ J) ▷ (Δ[1] : SSet)) ≫
        (dgModuleAugmentationUnliftedHomotopy R C E F).h
  simp only [comp_whiskerRight, Category.assoc]
  rw [dgModuleAugmentationUnliftedHomotopy_precomp R A C E H F]
end SerrePositivity.InfinityCategories
