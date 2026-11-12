module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedHomPostcomposition
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ReflectedBousfieldKanColimit

/-!
概要：coherent な錐に適合する反転係数の end に、反転した Hom 空間全体で後合成する。
方針：重み付き end の反転同型で豊穣作用を移し、coend の比較の豊穣自然性を反転する。
規約：反転した重みの coend を用い、end の同型の選択と合成を明示する。
使われ方：HTT 4.2.4.1 の反転 coend の普遍切断点から全比較族を復元する準備。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {I : Type u} [SmallCategory I]

/-- 反転した係数の end への、反転した内部 Hom 全体による実際の後合成。 -/
def reflectedWeightedHomPostcomposition (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u})
    (Y Z : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F Y ⋙ SSet.opFunctor) ⊗
        ((ihom Y).obj Z).op ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F Z ⋙ SSet.opFunctor) :=
  ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionsReflectedIso W (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F Y)).inv ▷
      ((ihom Y).obj Z).op) ≫
    (Functor.Monoidal.μIso SSet.opFunctor
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (W ⋙ SSet.opFunctor) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F Y))
      ((ihom Y).obj Z)).hom ≫
    SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedHomPostcomposition (W ⋙ SSet.opFunctor) F Y Z) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionsReflectedIso W (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F Z)).hom

/-- 反転 coend の比較は反転 Hom 全体の合成と可換。 -/
lemma reflectedWeightedColimitHomIso_enriched_naturality
    (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u}) (Y Z : SSet.{u}) :
    (Functor.Monoidal.μIso SSet.opFunctor
        ((ihom (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit (W ⋙ SSet.opFunctor) F)).obj Y)
        ((ihom Y).obj Z)).hom ≫
      SSet.opFunctor.map (MonoidalClosed.comp (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit (W ⋙ SSet.opFunctor) F) Y Z) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.reflectedWeightedColimitHomIso W F Z).hom =
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.reflectedWeightedColimitHomIso W F Y).hom ▷ ((ihom Y).obj Z).op) ≫
        reflectedWeightedHomPostcomposition W F Y Z := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.reflectedWeightedColimitHomIso, Iso.trans_hom, Functor.mapIso_hom,
    reflectedWeightedHomPostcomposition, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomIso]
  simp only [comp_whiskerRight_assoc]
  rw [← comp_whiskerRight_assoc
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionsReflectedIso W (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F Y)).hom]
  rw [Iso.hom_inv_id, MonoidalCategory.id_whiskerRight, Category.id_comp]
  rw [← Functor.map_comp_assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomComparison_enriched_naturality,
    Functor.map_comp]
  simp only [Category.assoc]
  rfl

/-- 反転 coend の置換射を前合成した比較も反転 Hom 全体の合成を保つ。 -/
lemma reflectedWeightedColimitHomComparison_pre_enriched_naturality
    (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u}) {K : SSet.{u}}
    (j : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit (W ⋙ SSet.opFunctor) F ⟶ K) (Y Z : SSet.{u}) :
    (Functor.Monoidal.μIso SSet.opFunctor ((ihom K).obj Y) ((ihom Y).obj Z)).hom ≫
        SSet.opFunctor.map (MonoidalClosed.comp K Y Z) ≫
          SSet.opFunctor.map ((pre j).app Z) ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.reflectedWeightedColimitHomIso W F Z).hom =
      ((SSet.opFunctor.map ((pre j).app Y) ≫
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.reflectedWeightedColimitHomIso W F Y).hom) ▷ ((ihom Y).obj Z).op) ≫
        reflectedWeightedHomPostcomposition W F Y Z := by
  rw [← Functor.map_comp_assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.internalHom_comp_pre, Functor.map_comp]
  have ht :
      (Functor.Monoidal.μIso SSet.opFunctor ((ihom K).obj Y) ((ihom Y).obj Z)).hom ≫
          SSet.opFunctor.map ((pre j).app Y ▷ (ihom Y).obj Z) =
        (SSet.opFunctor.map ((pre j).app Y) ▷ ((ihom Y).obj Z).op) ≫
          (Functor.Monoidal.μIso SSet.opFunctor
            ((ihom (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit (W ⋙ SSet.opFunctor) F)).obj Y)
            ((ihom Y).obj Z)).hom := rfl
  simp only [Category.assoc]
  rw [← Category.assoc _ (SSet.opFunctor.map ((pre j).app Y ▷ (ihom Y).obj Z)), ht]
  rw [Category.assoc, reflectedWeightedColimitHomIso_enriched_naturality,
    comp_whiskerRight_assoc]

/-- 置換射の反転像を表す、反転係数の end の普遍切断点。 -/
def reflectedWeightedColimitHomPointOfMap
    (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u}) {K : SSet.{u}}
    (j : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit (W ⋙ SSet.opFunctor) F ⟶ K) :
    𝟙_ SSet.{u} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F K ⋙ SSet.opFunctor) :=
  (Functor.Monoidal.εIso SSet.opFunctor).hom ≫ SSet.opFunctor.map (curry' j) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.reflectedWeightedColimitHomIso W F K).hom

/-- 反転 Hom の全比較族を、置換射の普遍切断点と反転した豊穣後合成から復元する。 -/
lemma reflectedWeightedColimitHomComparison_pre_of_point
    (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u}) {K : SSet.{u}}
    (j : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit (W ⋙ SSet.opFunctor) F ⟶ K) (Y : SSet.{u}) :
    (λ_ ((ihom K).obj Y).op).inv ≫
        (reflectedWeightedColimitHomPointOfMap W F j ▷ ((ihom K).obj Y).op) ≫
          reflectedWeightedHomPostcomposition W F K Y =
      SSet.opFunctor.map ((pre j).app Y) ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.reflectedWeightedColimitHomIso W F Y).hom := by
  dsimp only [reflectedWeightedColimitHomPointOfMap, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.reflectedWeightedColimitHomIso,
    Iso.trans_hom, Functor.mapIso_hom, reflectedWeightedHomPostcomposition,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomIso]
  simp only [comp_whiskerRight_assoc]
  rw [← comp_whiskerRight_assoc
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionsReflectedIso W (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F K)).hom]
  rw [Iso.hom_inv_id, MonoidalCategory.id_whiskerRight, Category.id_comp]
  change SSet.opFunctor.map
      ((λ_ ((ihom K).obj Y)).inv ≫
        ((curry' j ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomComparison (W ⋙ SSet.opFunctor) F K) ▷
          (ihom K).obj Y) ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedHomPostcomposition (W ⋙ SSet.opFunctor) F K Y) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionsReflectedIso W (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F Y)).hom = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomComparison_pre_of_point, Functor.map_comp, Category.assoc]

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
