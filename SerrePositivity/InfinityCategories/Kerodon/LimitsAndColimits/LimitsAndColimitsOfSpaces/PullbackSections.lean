module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.CoherentConeSectionSpace

/-!
概要：図式に沿う引き戻しの切断空間と、元の射の相対関手空間の同型。
方針：引き戻しの普遍性で底の図式に重なる族を切断の族へ移す。
規約：全ての単体集合の射を扱い、充填性を要求しない。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の coherent な錐の left fibration 上の切断表示。

対応節は Kerodon 7.4（Tag 02SX）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-- 概要：相対関手の族の評価は任意のパラメータの前合成と可換。
方針：内部 Hom の uncurry の前合成の自然性を使う。
規約：底の指定図式は任意の射。
使われ方：Kerodon 5.3.1.5（Tag 035J）、7.4.1.6（Tag 05QS） の引き戻しの切断模型の比較。 -/
lemma relativeFunctorUncurry_parameter {K E B A A' : SSet.{u}} {p : E ⟶ B} {a : K ⟶ B}
    (f : A' ⟶ A) (g : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p a) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (f ≫ g) = (K ◁ f) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry g := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry
  rw [Category.assoc, uncurry_natural_left]

/-- 概要：引き戻しの第二射影の切断空間は指定図式上の相対関手空間と同型。
方針：両模型の普遍的な族を引き戻しへ持ち上げ、評価の一意性で両逆関係を示す。
規約：引き戻す写像と図式に fibration 性や Kan 性は要求しない。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の coslice の図式への制限と切断空間の比較。 -/
noncomputable def pullbackSectionsRelativeIso {K E B : SSet.{u}} (p : E ⟶ B) (a : K ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections (pullback.snd p a) ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p a := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation (pullback.snd p a)
  let u := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p a))
  have he : (e ≫ pullback.fst p a) ≫ p =
      fst K (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections (pullback.snd p a)) ≫ a := by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation (pullback.snd p a) ≫ pullback.snd p a) ≫ a = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation_projection]
  let h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorCurry (p := p) (a := a) (e ≫ pullback.fst p a) he
  let l := pullback.lift u (fst K (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p a))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_projection _)
  let g := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsLift (p := pullback.snd p a) l (pullback.lift_snd _ _ _)
  have hh : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry h = e ≫ pullback.fst p a := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_curry _ _
  have hg : (K ◁ g) ≫ e = l := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsLift_evaluation _ _
  refine ⟨h, g, ?_, ?_⟩
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections_hom_ext
    rw [whiskerLeft_comp, Category.assoc]
    change (K ◁ h) ≫ ((K ◁ g) ≫ e) = (K ◁ 𝟙 _) ≫ e
    rw [hg, whiskerLeft_id, Category.id_comp]
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst]
      change (K ◁ h) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p a)) = _
      rw [← relativeFunctorUncurry_parameter, Category.comp_id, hh]
    · rw [Category.assoc, pullback.lift_snd, whiskerLeft_fst]
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation_projection (pullback.snd p a)).symm
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_injective p a
    rw [relativeFunctorUncurry_parameter, hh, ← Category.assoc, hg]
    exact pullback.lift_fst _ _ _

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
