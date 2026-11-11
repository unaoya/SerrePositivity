module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.RelativeFunctorInverse

/-! # 底上の合成と同値との相対三角形から、同じ比較の底上の右逆を回収する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.KST.Fibration
open SerrePositivity.InfinityCategories

/-- 相対三角形の合成が底上の同値なら、後の比較には同じ底を保つホモトピー右逆がある。 -/
theorem exists_relativeRightSection_of_compositeIso
    {A E F B : SSet.{u}} [Quasicategory B]
    (pA : A ⟶ B) (pE : E ⟶ B) (pF : F ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration pA] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration pF]
    (u : A ⟶ E) (t : E ⟶ F) (g : A ⟶ F)
    (hu : u ≫ pE = pA) (ht : t ≫ pF = pE) (hg : g ≫ pF = pA)
    (eg : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence g)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex pF pA (u ≫ t) (by rw [Category.assoc, ht, hu]))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex pF pA g hg)) :
    ∃ (r : F ⟶ E) (hr : r ≫ pE = pF), Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex pF pF (r ≫ t) (by rw [Category.assoc, ht, hr]))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex pF pF (𝟙 F) (Category.id_comp pF))) := by
  obtain ⟨v, hv, _, ⟨hc⟩⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_relativeFunctorInverse_of_precompositionEquivalence pA pF g hg eg
  let v' : Over.mk pF ⟶ Over.mk pA := Over.homMk v hv
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre pF v')
  have hr : (v ≫ u) ≫ pE = pF := by rw [Category.assoc, hu, hv]
  refine ⟨v ≫ u, hr, ⟨?_⟩⟩
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex pF pF ((v ≫ u) ≫ t) (by rw [Category.assoc, ht, hr]))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex pF pF (v ≫ g) (by rw [Category.assoc, hg, hv])) at he
  exact he ≪≫ hc

end SerrePositivity.KST.Fibration
