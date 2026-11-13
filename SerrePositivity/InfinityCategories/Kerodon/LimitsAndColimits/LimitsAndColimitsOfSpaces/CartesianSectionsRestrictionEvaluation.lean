module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.CartesianSectionsRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ReflectedStrictConeEvaluation

/-!
概要：指定引き戻し表示の切断と相対関手の同型を、全評価で追跡する。
方針：既存の切断関手と引き戻し切断の評価式を合成する。
規約：任意のパラメータを保持し、fibration 性は要求しない。
使われ方：形状制限の二経路を同じ相対写像空間で比較する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-- 同じ指定引き戻し表示の相対比較の評価は、元の評価の第一射影。 -/
lemma sectionsRestrictionTargetIso_evaluation {E E' B K T : SSet.{u}}
    (p : E ⟶ B) (q : E' ⟶ K) (i : K ⟶ B)
    (e : E' ≅ pullback p i) (he : e.hom ≫ pullback.snd p i = q)
    (a : T ⟶ simplicialSections q) :
    relativeFunctorUncurry (a ≫ (sectionsRestrictionTargetIso p q i e he).hom) =
      (K ◁ a) ≫ simplicialSectionsEvaluation q ≫ e.hom ≫ pullback.fst p i := by
  dsimp only [sectionsRestrictionTargetIso, Iso.trans_hom]
  rw [relativeFunctorUncurry_parameter, relativeFunctorUncurry_parameter,
    pullbackSectionsRelativeIso_hom_uncurry]
  change (K ◁ a) ≫ (K ◁ simplicialSectionsMap e.hom he) ≫
    simplicialSectionsEvaluation (pullback.snd p i) ≫ pullback.fst p i = _
  rw [← Category.assoc (K ◁ simplicialSectionsMap e.hom he),
    simplicialSectionsMap_evaluation]
  simp only [Category.assoc]

/-- 相対表示へ送った実切断制限を評価すると、元の全評価の形状制限。 -/
lemma sectionsRestrictionOfIso_relative_evaluation {E E' B K : SSet.{u}}
    (p : E ⟶ B) (q : E' ⟶ K) (i : K ⟶ B)
    (e : E' ≅ pullback p i) (he : e.hom ≫ pullback.snd p i = q) :
    relativeFunctorUncurry
      (sectionsRestrictionOfIso p q i e he ≫ (sectionsRestrictionTargetIso p q i e he).hom) =
      (i ▷ simplicialSections p) ≫ simplicialSectionsEvaluation p := by
  rw [sectionsRestrictionTargetIso_evaluation]
  exact sectionsRestrictionOfIso_evaluation p q i e he

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
