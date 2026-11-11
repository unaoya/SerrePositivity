module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceEdgeFamilyCylinder
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.TrivialFibrationIsoFaithful
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ArrowLeftIdentityCancellation
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FunctorHomSquareRealization
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.HomotopyEndpointTransport

/-!
概要：動く終端を持つ同じ辺族間円柱に対し、元の切断比較円柱の自然性正方形を構成する。
方針：終端へ写した二つの積の恒等因子を消し、自明 Kan 制限の h Fun 上の忠実性で戻す。
規約：族間円柱・終端の切断像・両切断比較の四辺を保持。終端固定を追加仮定しない。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
noncomputable section
variable {X T : SSet.{u}} [Quasicategory X] (e : (Δ[1] : SSet.{u}) ⟶ X)
  (y : X _⦋0⦌) {F G : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace e y} (H : SSet.Homotopy F G)
local notation "r" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap e (stdSimplex.δ (0 : Fin 2)) y
local notation "s" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeSectionFiber e y
local notation "CF" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceEdgeFamilyCylinder.homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeFamilyCylinder e y F)
local notation "CG" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceEdgeFamilyCylinder.homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeFamilyCylinder e y G)

/-- 元の族間円柱の終端を同じ切断で戻し、両切断比較と同じ型付き端点へ揃える。 -/
def cosliceEdgeFamilySectionHomotopy : SSet.Homotopy ((F ≫ r) ≫ s) ((G ≫ r) ≫ s) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyEndpointTransport (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H (r ≫ s))
    (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm

/-- 終端の切断像も、元の同じ族間円柱の raw な像を保持する。 -/
lemma cosliceEdgeFamilySectionHomotopy_raw :
    (cosliceEdgeFamilySectionHomotopy e y H).h = H.h ≫ (r ≫ s) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyEndpointTransport_raw _ _ _

/-- 動く終端を同じ切断で戻す二経路は、元の指定した四円柱の同じ合成の類を持つ。 -/
lemma cosliceEdgeFamilyNaturality_homMk_comp :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy CF) ≫
        SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
          (cosliceEdgeFamilySectionHomotopy e y H)) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) ≫
        SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy CG) := by
  let J := cosliceEdgeFamilySectionHomotopy e y H
  let I₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy CF
  let I₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy J
  let I₂ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy H
  let I₃ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy CG
  let P := (hoFunctor.map ((ihom T).map r)).toFunctor
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceTriangleTarget_trivialKanFibration e y
  have h₀ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyIso_postcomp_constant_arrow CF r (F ≫ r)
    (by simpa only [Category.assoc] using (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeFamilyCylinder e y F).target)
  have h₃ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyIso_postcomp_constant_arrow CG r (G ≫ r)
    (by simpa only [Category.assoc] using (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeFamilyCylinder e y G).target)
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorIso_postcomp_hom] at h₀ h₃
  have hj := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomotopy_hom_arrow_of_h_eq
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp J r) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H r) (by
      change J.h ≫ r = H.h ≫ r
      dsimp only [J]
      rw [cosliceEdgeFamilySectionHomotopy_raw]
      simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeSectionFiber_target]
      exact congrArg (H.h ≫ ·) (Category.comp_id r))
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom] at hj
  have hL := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowLeftIdentity_cancel (P.map I₀.hom) (P.map I₁.hom)
    (P.map (I₀ ≪≫ I₁).hom) (P.map_comp _ _).symm h₀
  have hR := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowRightIdentity_cancel (P.map I₂.hom) (P.map I₃.hom)
    (P.map (I₂ ≪≫ I₃).hom) (P.map_comp _ _).symm h₃
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.trivialKanFibration_postcomp_iso_hom_injective r (I₀ ≪≫ I₁) (I₂ ≪≫ I₃)
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorIso_postcomp_hom, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorIso_postcomp_hom]
  exact hL.symm.trans (hj.trans hR)

/-- 同じ二つの切断比較と元の族間円柱・終端の切断像を四辺に保つ実際の正方形。 -/
def cosliceEdgeFamilyNaturalitySquare :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomSquare CF CG H (cosliceEdgeFamilySectionHomotopy e y H) :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonempty_functorHomSquare_of_homEq CF CG H (cosliceEdgeFamilySectionHomotopy e y H)
    (cosliceEdgeFamilyNaturality_homMk_comp e y H)).some

end
end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
