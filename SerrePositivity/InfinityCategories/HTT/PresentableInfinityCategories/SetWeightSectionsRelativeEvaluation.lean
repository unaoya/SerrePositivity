module

public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.SetWeightSectionsPrefixFactorization
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SectionsFiberwiseEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.CartesianSectionsRestrictionEvaluation

/-!
概要：元の相対切断同型の逆を、指定引き戻しの実評価で計算する。
方針：既存の切断・相対関手同型の自然性で、同じ引き戻し表示へ戻す。
規約：元の同型を保ち、任意のパラメータで評価する。
使われ方：G8 の四角形①で、実切断制限を相対前合成へ移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories

variable {I : Type u} [SmallCategory I] (X : I ⥤ Type u)
  (G : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ SpaceInfinity.{u})

/-- 元の相対切断同型の逆は、同じ指定引き戻しの切断比較である。 -/
lemma setWeightRelativeSectionsIso_inv :
    (setWeightRelativeSectionsIso X G).inv =
      (sectionsRestrictionTargetIso (smallLeftUnstraighteningProjection G)
        (smallLeftUnstraighteningProjection (SetWeight.diagram X G)) (SetWeight.projection X)
        (smallLeftUnstraighteningBaseChangeIso G (SetWeight.projection X))
        (smallLeftUnstraighteningBaseChangeIso_hom_snd G (SetWeight.projection X))).hom := by
  let q := smallLeftUnstraighteningProjection G
  let p := SetWeight.projection X
  let q' := smallLeftUnstraighteningProjection (SetWeight.diagram X G)
  let bp : Over.mk q' ≅ Over.mk (pullback.snd q p) :=
    Over.isoMk (smallLeftUnstraighteningBaseChangeIso G p)
      (smallLeftUnstraighteningBaseChangeIso_hom_snd G p)
  apply (cancel_mono (setWeightRelativeSectionsIso X G).hom).mp
  rw [Iso.inv_hom_id]
  change 𝟙 _ =
    (simplicialSectionsFunctor _).map bp.hom ≫ (pullbackSectionsRelativeIso q p).hom ≫
      ((pullbackSectionsRelativeIso q p).inv ≫ (simplicialSectionsRelativeIso _).hom ≫
        (relativeFunctorOverIso (Iso.refl (Over.mk (𝟙 _))) bp.symm).hom ≫
          (simplicialSectionsRelativeIso q').inv)
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  change 𝟙 _ = simplicialSectionsMap bp.hom.left bp.hom.w ≫
    (simplicialSectionsRelativeIso _).hom ≫ _ ≫ _
  rw [← Category.assoc (simplicialSectionsMap bp.hom.left bp.hom.w),
    simplicialSectionsRelativeIso_naturality]
  simp only [relativeFunctorOverIso_hom, Iso.refl_inv, relativeFunctorOverPre_id,
    Category.id_comp, Category.assoc]
  change 𝟙 _ = (simplicialSectionsRelativeIso q').hom ≫
    ((relativeFunctorOverPostFunctor (𝟙 _)).map bp.hom ≫
      (relativeFunctorOverPostFunctor (𝟙 _)).map bp.inv) ≫ _
  rw [← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  change 𝟙 _ = (simplicialSectionsRelativeIso q').hom ≫ 𝟙 _ ≫
    (simplicialSectionsRelativeIso q').inv
  rw [Category.id_comp, Iso.hom_inv_id]

/-- 元の切断表示から相対表示への全評価は、元の小さい底変換射との合成。 -/
lemma setWeightRelativeSectionsIso_inv_evaluation {T : SSet.{u}}
    (a : T ⟶ simplicialSections
      (smallLeftUnstraighteningProjection (SetWeight.diagram X G))) :
    relativeFunctorUncurry (a ≫ (setWeightRelativeSectionsIso X G).inv) =
      (nerve X.Elements ◁ a) ≫
        simplicialSectionsEvaluation (smallLeftUnstraighteningProjection (SetWeight.diagram X G)) ≫
          smallLeftUnstraighteningMap (SetWeight.diagram X G) G (SetWeight.projection X) rfl := by
  rw [setWeightRelativeSectionsIso_inv, sectionsRestrictionTargetIso_evaluation]
  simp only [← Category.assoc]
  have he : (smallLeftUnstraighteningBaseChangeIso G (SetWeight.projection X)).hom ≫
      pullback.fst (smallLeftUnstraighteningProjection G) (SetWeight.projection X) =
      smallLeftUnstraighteningMap (SetWeight.diagram X G) G (SetWeight.projection X) rfl :=
    IsPullback.isoPullback_hom_fst _
  rw [Category.assoc _ (smallLeftUnstraighteningBaseChangeIso G (SetWeight.projection X)).hom, he]

end SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
