module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceEdgeSectionFiber

/-!
概要：指定した辺全体の余錐族を、その辺による実際の前合成と全パラメータで比較する。
方針：終点評価の自明 Kan fibration 上で切断と比較し、両端の表示を正規化する。
規約：元の辺と可変終点を保持し、パラメータの Kan 性を要求しない。
使われ方：native な共通脚に制限した四面体の族を Hom の前合成と照合する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {X T : SSet.{u}} [Quasicategory X] (e : (Δ[1] : SSet.{u}) ⟶ X)
  (y : X _⦋0⦌) (F : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace e y)

/-- 指定した全辺の族と切断による族を、終点族を保つホモトピーで結ぶ。 -/
lemma cosliceEdgeFamily_section_homotopy :
    ∃ H : SSet.Homotopy F
      ((F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap e (stdSimplex.δ (0 : Fin 2)) y) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeSectionFiber e y),
      H.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap e (stdSimplex.δ (0 : Fin 2)) y =
        fst T (Δ[1] : SSet.{u}) ≫ F ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap e (stdSimplex.δ (0 : Fin 2)) y := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceTriangleTarget_trivialKanFibration e y
  have hs : ((F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap e (stdSimplex.δ (0 : Fin 2)) y) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeSectionFiber e y) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap e (stdSimplex.δ (0 : Fin 2)) y =
        F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap e (stdSimplex.δ (0 : Fin 2)) y := by
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeSectionFiber_target]
    exact Category.comp_id _
  obtain ⟨H, hH⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_homotopy_over_trivialKanFibration
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap e (stdSimplex.δ (0 : Fin 2)) y) F
    ((F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap e (stdSimplex.δ (0 : Fin 2)) y) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeSectionFiber e y) hs.symm
  refine ⟨H, hH.trans ?_⟩
  simpa only [Category.assoc] using congrArg
    (fun k ↦ fst T (Δ[1] : SSet.{u}) ≫ k) hs

/-- 両端を指定した実際の辺全体の族の始点側は、終点側と実際の前合成の合成にホモトピック。 -/
lemma cosliceEdgeFamily_precomposition_homotopy
    (a b : (Δ[0] : SSet.{u}) ⟶ X)
    (ha : stdSimplex.δ (1 : Fin 2) ≫ e = a)
    (hb : stdSimplex.δ (0 : Fin 2) ≫ e = b) :
    Nonempty (SSet.Homotopy
      (F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber e (stdSimplex.δ (1 : Fin 2)) ha y)
      ((F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber e (stdSimplex.δ (0 : Fin 2)) hb y) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeFiberPrecomposition e a b ha hb y)) := by
  cases hb
  obtain ⟨H, _⟩ := cosliceEdgeFamily_section_homotopy e y F
  have H' : Nonempty (SSet.Homotopy
      (F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber e (stdSimplex.δ (1 : Fin 2)) ha y)
      ((F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap e (stdSimplex.δ (0 : Fin 2)) y) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeFiberPrecomposition e a (stdSimplex.δ (0 : Fin 2) ≫ e) ha rfl y)) := by
    exact ⟨by simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeSectionFiber_source] using
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber e (stdSimplex.δ (1 : Fin 2)) ha y))⟩
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber_eq, eqToHom_refl, Category.comp_id] using H'

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
