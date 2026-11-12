module

public import SerrePositivity.KST.Spectra.ConstantHomotopyEndIso
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictConeWeightedEvaluation

/-!
概要：定値 homotopy end の写像空間比較を普遍評価で計算する。
方針：切断の比較の評価式を直積の第二射影へ合成する。
規約：構成済みの同型そのものの順射を計算する。
使われ方：Goerss–Jardine VIII §2。自明作用の標準射と基点の照合。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (C : Type u) [SmallCategory C] (X : SSet.{u})

@[reassoc]
lemma constantSectionsIso_inv_evaluation :
    (nerve C ◁ ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsFunctor (nerve C)).mapIso
      (constantWeightedNerveOverIso C X)).inv) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation (fst (nerve C) X) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection ((Functor.const C).obj X)) ≫
        constantWeightedNerveToProduct C X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsMap_evaluation (constantWeightedNerveOverIso C X).inv.left
    (Over.w (constantWeightedNerveOverIso C X).inv)

/-- 概要：定値 homotopy end の写像空間同型の評価は weighted nerve の係数評価。
方針：切断の普遍評価と直積の第二射影による評価を合成する。
規約：実際の同型の順射を uncurry した厳密な等式。
使われ方：Goerss–Jardine VIII §2。標準比較射の写像空間での具体式。 -/
lemma constantHomotopyEndIso_uncurry :
    uncurry (constantHomotopyEndIso C X).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeightedNerveEvaluation ((Functor.const C).obj X) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveConstantEvaluation C X := by
  let H := (Functor.const C).obj X
  let t := ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsFunctor (nerve C)).mapIso
    (constantWeightedNerveOverIso C X)).inv
  change uncurry ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanSectionsMap H ≫ t) ≫ productSectionsToHom (nerve C) X) = _
  rw [uncurry_natural_left, productSectionsToHom_uncurry, whiskerLeft_comp]
  have h := constantSectionsIso_inv_evaluation C X
  change (nerve C ◁ t) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation (fst (nerve C) X) = _ at h
  calc
    _ = (nerve C ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanSectionsMap H) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection H) ≫
          constantWeightedNerveToProduct C X) ≫ snd (nerve C) X := by
      simpa only [Category.assoc] using
        congrArg (fun z ↦ (nerve C ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanSectionsMap H) ≫ z ≫ snd (nerve C) X) h
    _ = ((nerve C ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanSectionsMap H) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection H)) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveConstantEvaluation C X := by
      simp [constantWeightedNerveToProduct, Category.assoc]
    _ = _ := by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanSectionsMap_evaluation]

end

end SerrePositivity.KST.Spectra
