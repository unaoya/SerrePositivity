module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorUniversePostNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallLeftUnstraighteningOverMap
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallLeftUnstraighteningMappingSpace

/-!
概要：元の小さい相対表示と大きい表示の指定同型は、標的の同じ実射の後合成に自然。
方針：宇宙変更と同型による共役の自然性を順に適用する。
規約：縮小写像とその元の同型を保持し、別の自然性同型を選ばない。
使われ方：G14 の小さい Yoneda 評価の後合成比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 元の大小の相対写像空間の比較は、縮小した同じ全空間の射の後合成と厳密に可換。 -/
lemma smallLeftUnstraighteningRelativeFunctorIso_post {B : SSet.{u}}
    (F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (f : leftUnstraightening G ⟶ leftUnstraightening J)
    (hf : f ≫ leftUnstraighteningProjection J = leftUnstraighteningProjection G) :
    (SSet.uliftFunctor.{u + 1, u}).map
      (relativeFunctorPost (smallLeftUnstraighteningProjection G) (smallLeftUnstraighteningProjection J)
        (smallLeftUnstraighteningOverMap G J f)
        (smallLeftUnstraighteningOverMap_projection G J f hf) (smallLeftUnstraighteningProjection F)) ≫
      (smallLeftUnstraighteningRelativeFunctorIso F J).hom =
    (smallLeftUnstraighteningRelativeFunctorIso F G).hom ≫
      relativeFunctorPost (leftUnstraighteningProjection G) (leftUnstraighteningProjection J)
        f hf (leftUnstraighteningProjection F) := by
  simp only [smallLeftUnstraighteningRelativeFunctorIso, Iso.trans_hom, Category.assoc]
  change _ ≫ uliftRelativeFunctorMap _ _ ≫ _ = uliftRelativeFunctorMap _ _ ≫ _
  rw [← Category.assoc, uliftRelativeFunctorMap_post, Category.assoc]
  have hs : (SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningOverMap G J f) ≫
      (smallLeftUnstraighteningIso J).hom = (smallLeftUnstraighteningIso G).hom ≫ f :=
    smallLeftUnstraighteningOverMap_naturality G J f
  have h := relativeFunctorOverIso_post_hom (smallLeftUnstraighteningOverIso F)
    (smallLeftUnstraighteningOverIso G) (smallLeftUnstraighteningOverIso J)
    (Over.homMk ((SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningOverMap G J f))
      (by
        change (SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningOverMap G J f) ≫
          (SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningProjection J) =
          (SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningProjection G)
        rw [← Functor.map_comp, smallLeftUnstraighteningOverMap_projection G J f hf]))
    (Over.homMk f hf) (by
      apply Over.OverMorphism.ext
      exact hs.symm)
  dsimp only [Over.mk, Over.hom, CostructuredArrow.mk] at h
  exact congrArg (fun k => uliftRelativeFunctorMap (smallLeftUnstraighteningProjection G)
    (smallLeftUnstraighteningProjection F) ≫ k) h

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
