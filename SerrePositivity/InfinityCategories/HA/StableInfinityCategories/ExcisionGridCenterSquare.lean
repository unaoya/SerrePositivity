module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCenterSpanShapeIso

/-!
概要：中央の実正方形と同じ span の辺・頂点の厳密な比較。
方針：同じ実図式の native 余錐と頂点を保持して比較する。
規約：一般安定性を先取りしない。使われ方：HA 1.4.2.15 の中央面。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
variable {P : Type u} [PartialOrder P]

def excisionGridCenterSquare : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶
    nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreIndex.{u} where
  app n := ↾fun s ↦
    (⟨fun k ↦ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCorePoint ((stdSimplex.objEquiv s.1).toOrderHom k).succ
        ((stdSimplex.objEquiv s.2).toOrderHom k).succ,
      fun _ _ h ↦ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCorePoint_le
        (Nat.add_le_add_right ((stdSimplex.objEquiv s.1).toOrderHom.monotone h) 1)
        (Nat.add_le_add_right ((stdSimplex.objEquiv s.2).toOrderHom.monotone h) 1)⟩ :
      Fin (n.unop.len + 1) →o _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreIndex.{u}).toFunctor
  naturality := by
    intro n m α
    apply ConcreteCategory.hom_ext
    intro s
    apply CategoryTheory.Functor.ext
    · intro i j f; apply Subsingleton.elim
    · intro i; rfl

lemma excisionGridCenterSpanShapeIso_projection :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCenterSpanShapeIso.{u}.hom ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridPastIndex.{u})
        (fun v ↦ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridCenterSpan (nerveEquiv v))).ι ≫
          nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridPast) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan excisionGridCenterSquare := by
  change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpanIso.hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridPastingToCenterSpan ≫
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeNerveIso _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridCenterSpan).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridPastIndex.{u})
        (fun v ↦ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridCenterSpan (nerveEquiv v))).ι ≫
          nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridPast) = _
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeNerveIso _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridCenterSpan).hom,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeNerveIso_hom_ι]
  apply horn₂₀.isPushout.hom_ext
  · rw [← Category.assoc horn₂₀.ι₀₁ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpanIso.hom]
    change (horn₂₀.ι₀₁ ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpanFromHorn) ≫ _ = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpanFromHorn_left]
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan]
    rw [← Category.assoc horn₂₀.ι₀₁ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_bottomEdge]
    apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveHom_ext_of_vertices
    intro v
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective v
    fin_cases i <;> apply Subtype.ext <;> apply Subtype.ext <;> apply ULift.ext <;>
      apply Subtype.ext <;> apply Prod.ext <;> apply Fin.ext <;> decide
  · rw [← Category.assoc horn₂₀.ι₀₂ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpanIso.hom]
    change (horn₂₀.ι₀₂ ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpanFromHorn) ≫ _ = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpanFromHorn_right]
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan]
    rw [← Category.assoc horn₂₀.ι₀₂ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_leftEdge]
    apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveHom_ext_of_vertices
    intro v
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective v
    fin_cases i <;> apply Subtype.ext <;> apply Subtype.ext <;> apply ULift.ext <;>
      apply Subtype.ext <;> apply Prod.ext <;> apply Fin.ext <;> decide

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
