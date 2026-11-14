module

public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.SetWeightSectionsBigRelativeComparison
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.SetWeightSectionsRelativeNaturality

/-!
概要：元の切断同値の順射は、重みの元の辺による前合成と全族で自然である。
方針：大きい相対表示の四角形を、元の小さい切断表示へ戻す。
規約：同値の順射・実切断制限・元の辺の代表を保持する。
使われ方：G8 の篩包含の四角形①の中段。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
namespace SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories

variable {I : Type u} [SmallCategory I] {X Y : I ⥤ Type u} (φ : X ⟶ Y)
  (G : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ SpaceInfinity.{u})

/-- 元の大小の相対表示の比較は、同じ要素の圏の前合成と厳密に可換。 -/
lemma setWeightRelativeUniverseIso_restriction :
    (SSet.uliftFunctor.{u + 1, u}).map
      (relativeFunctorOverPre (smallLeftUnstraighteningProjection G)
        (show Over.mk (SetWeight.projection X) ⟶ Over.mk (SetWeight.projection Y) from
          Over.homMk (nerveMap φ.mapElements) (by rfl))) ≫
      (setWeightRelativeUniverseIso X G).hom =
    (setWeightRelativeUniverseIso Y G).hom ≫
      relativeFunctorOverPre (leftUnstraighteningProjection G) (setWeightElementsBaseMap φ) := by
  simp only [setWeightRelativeUniverseIso, Iso.trans_hom, Category.assoc]
  change _ ≫ uliftRelativeFunctorMap _ _ ≫ _ = uliftRelativeFunctorMap _ _ ≫ _
  rw [← Category.assoc, uliftRelativeFunctorMap_overPre, Category.assoc]
  erw [relativeFunctorOverIso_pre_hom _
    (Iso.refl (Over.mk ((SSet.uliftFunctor.{u + 1, u}).map (SetWeight.projection Y))))
      (smallLeftUnstraighteningOverIso G)]

/-- 元の小さい切断制限と大きい相対表示への比較は、同じ前合成で厳密に可換。 -/
lemma setWeightSectionsBigRelativeIso_restriction :
    (SSet.uliftFunctor.{u + 1, u}).map (setWeightActualSectionsRestriction φ G) ≫
      (setWeightSectionsBigRelativeIso X G).hom =
    (setWeightSectionsBigRelativeIso Y G).hom ≫
      relativeFunctorOverPre (leftUnstraighteningProjection G) (setWeightElementsBaseMap φ) := by
  simp only [setWeightSectionsBigRelativeIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Category.assoc]
  rw [← Category.assoc, ← Functor.map_comp, setWeightRelativeSectionsIso_restriction,
    Functor.map_comp, Category.assoc, setWeightRelativeUniverseIso_restriction]

/-- 元の切断同値の順射と元の重みの辺の前合成は、実切断制限と全族で自然である。 -/
def setWeightSectionsEquivalenceNatural_shapeIso :
    FunctorIso
      (precompose (functorVertex G)
        (SSet.Truncated.HomotopyCategory.homMk (SetWeight.spaceDiagramEdge φ).toTruncated) ≫
          (SetWeight.sectionsEquivalenceNatural X G).hom)
      ((SetWeight.sectionsEquivalenceNatural Y G).hom ≫
        (SSet.uliftFunctor.{u + 1, u}).map (setWeightActualSectionsRestriction φ G)) := by
  have h := (setWeightBigRelativePrefix_naturality φ G).postcomp
    (setWeightSectionsBigRelativeIso X G).inv
  rw [← setWeightSectionsEquivalenceNatural_bigRelative X G,
    ← setWeightSectionsEquivalenceNatural_bigRelative Y G] at h
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h
  have he := congrArg (fun f ↦ f ≫ (setWeightSectionsBigRelativeIso X G).inv)
    (setWeightSectionsBigRelativeIso_restriction φ G)
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at he
  rw [← he] at h
  exact h

end SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
