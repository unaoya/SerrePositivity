module

public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.SetWeightSectionsRelativeEvaluation
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.SetWeightActualSectionsRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.SmallSectionsShapeNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorSquarePost

/-!
概要：元の小さい切断制限を、同じ底上の相対前合成へ移す。
方針：全評価で比較し、既存の底変換射の合成則と切断制限の評価を使う。
規約：図式の表示の等式を保持し、全パラメータについて厳密な等式を示す。
使われ方：G8 の四角形①で、相対自然性を元の切断同値へ接続する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
namespace SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories

/-- 指定表示へ正規化した実切断制限も、元の底変換射による全評価を保つ。 -/
lemma normalizedSmallSectionsRestriction_map_evaluation {B K : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (G : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ SpaceInfinity.{u})
    (i : K ⟶ B) (hi : (SSet.uliftFunctor.{u + 1, u}).map i ≫ F = G) :
    (K ◁ normalizedSmallSectionsRestriction F G i hi) ≫
      simplicialSectionsEvaluation (smallLeftUnstraighteningProjection G) ≫
        smallLeftUnstraighteningMap G F i hi =
      (i ▷ simplicialSections (smallLeftUnstraighteningProjection F)) ≫
        simplicialSectionsEvaluation (smallLeftUnstraighteningProjection F) := by
  subst G
  simpa only [normalizedSmallSectionsRestriction, eqToHom_refl, Category.comp_id] using
    smallUnstraighteningSectionsRestriction_map_evaluation F i

/-- 元の小さい切断制限は、元の相対表示への同型の逆と厳密に可換。 -/
lemma setWeightRelativeSectionsIso_restriction {I : Type u} [SmallCategory I]
    {X Y : I ⥤ Type u} (φ : X ⟶ Y)
    (G : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ SpaceInfinity.{u}) :
    setWeightActualSectionsRestriction φ G ≫ (setWeightRelativeSectionsIso X G).inv =
      (setWeightRelativeSectionsIso Y G).inv ≫
        relativeFunctorOverPre (smallLeftUnstraighteningProjection G)
          (show Over.mk (SetWeight.projection X) ⟶ Over.mk (SetWeight.projection Y) from
            Over.homMk (nerveMap φ.mapElements) (by rfl)) := by
  apply relativeFunctorUncurry_injective
  erw [relativeFunctorOverPre_uncurry, setWeightRelativeSectionsIso_inv_evaluation]
  have hy := setWeightRelativeSectionsIso_inv_evaluation Y G (𝟙 _)
  simp only [Category.id_comp, whiskerLeft_id] at hy
  erw [hy]
  have hc := smallLeftUnstraighteningMap_comp
    (SetWeight.diagram X G) (SetWeight.diagram Y G) G
    (nerveMap φ.mapElements) (SetWeight.projection Y) (SetWeight.elementsMap_diagram φ G) rfl
  change _ ≫ _ ≫ smallLeftUnstraighteningMap (SetWeight.diagram X G) G
    (SetWeight.projection X) rfl = _
  rw [show smallLeftUnstraighteningMap (SetWeight.diagram X G) G (SetWeight.projection X) rfl =
    smallLeftUnstraighteningMap (SetWeight.diagram X G) (SetWeight.diagram Y G)
      (nerveMap φ.mapElements) (SetWeight.elementsMap_diagram φ G) ≫
    smallLeftUnstraighteningMap (SetWeight.diagram Y G) G (SetWeight.projection Y) rfl from hc]
  simp only [← Category.assoc]
  congr 1
  exact normalizedSmallSectionsRestriction_map_evaluation
    (SetWeight.diagram Y G) (SetWeight.diagram X G) (nerveMap φ.mapElements)
    (SetWeight.elementsMap_diagram φ G)

end SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
