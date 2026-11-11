module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridRightSquare

/-!
概要：同じ実正方形の二辺と native 下方添字の射影を比較する。
方針：同じ実図式の native 余錐・頂点・二辺を保持して比較する。
規約：一般安定性を先取りしない。使われ方：HA 1.4.2.15 の外側の面。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

lemma excisionGridRightSpanShapeIso_projection :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridRightSpanShapeIso.{u}.hom ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridRightLowerIndex.{u})
        (fun v ↦ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridRightSpan (nerveEquiv v))).ι ≫
      nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerProjection _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridMiddle _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridPoint32) ≫
        nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridMiddleInclusion = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridRightSquare := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridRightSpanShapeIso, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc]
  apply horn₂₀.isPushout.hom_ext
  · rw [← Category.assoc horn₂₀.ι₀₁ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpanIso.hom]
    change (horn₂₀.ι₀₁ ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpanFromHorn) ≫ _ = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpanFromHorn_left]
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan]
    rw [← Category.assoc horn₂₀.ι₀₁ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_bottomEdge]
    apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveHom_ext_of_vertices
    intro v
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective v
    fin_cases i <;> apply ULift.ext <;> apply Subtype.ext <;>
      apply Prod.ext <;> apply Fin.ext <;> decide
  · rw [← Category.assoc horn₂₀.ι₀₂ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpanIso.hom]
    change (horn₂₀.ι₀₂ ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpanFromHorn) ≫ _ = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpanFromHorn_right]
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan]
    rw [← Category.assoc horn₂₀.ι₀₂ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_leftEdge]
    apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveHom_ext_of_vertices
    intro v
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective v
    fin_cases i <;> apply ULift.ext <;> apply Subtype.ext <;>
      apply Prod.ext <;> apply Fin.ext <;> decide

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
