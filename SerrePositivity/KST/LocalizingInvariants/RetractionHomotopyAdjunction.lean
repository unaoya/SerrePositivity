module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.AdjunctionHomTriangles
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.PrecompositionHomotopy

/-!
概要：厳密な引き戻し恒等と両三角の定値ホモトピーから実随伴を構成する。
方針：単位の前後合成を端点輸送の射へ戻し、h Fun 全体で三角恒等式を証明する。
規約：h X と h Y の随伴へ弱めない。使われ方：矢印圏の終点評価の随伴。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

variable {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
  {F : X ⟶ Y} {G : Y ⟶ X} (h : G ≫ F = 𝟙 Y)
  (H : SSet.Homotopy (𝟙 X) (F ≫ G))
  (hF : H.h ≫ F = fst X (Δ[1] : SSet.{u}) ≫ F)
  (hG : (G ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst Y (Δ[1] : SSet.{u}) ≫ G)

def retractionCounit : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (G ≫ F) (𝟙 Y) :=
  eqToHom (congrArg (fun f ↦ HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)) h)

def retractionHomotopyUnit : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G) :=
  Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)

include hF in
lemma retractionHomotopy_leftTriangle :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitLeftZigzag (retractionHomotopyUnit H) (retractionCounit h) =
      𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitLeftZigzag retractionHomotopyUnit
  rw [← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom]
  have he : (𝟙 X) ≫ F = (F ≫ G) ≫ F := by
    rw [Category.id_comp, Category.assoc, h, Category.comp_id]
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homotopyHom_eqToHom (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H F) he (by
    change H.h ≫ F = fst X (Δ[1] : SSet.{u}) ≫ ((𝟙 X) ≫ F)
    simpa only [Category.id_comp] using hF)]
  simp only [retractionCounit, eqToHom_map, eqToHom_trans, eqToHom_refl]

omit [Quasicategory X] [Quasicategory Y] in
include hG in
lemma retractionHomotopy_rightTriangle :
    (hoFunctor.map ((pre G).app X)).toFunctor.map (retractionHomotopyUnit H) ≫
      (hoFunctor.map ((ihom Y).map G)).toFunctor.map (retractionCounit h) =
        𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)) := by
  unfold retractionHomotopyUnit
  rw [← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp_hom]
  have he : G ≫ (𝟙 X) = G ≫ (F ≫ G) := by
    rw [Category.comp_id, ← Category.assoc, h, Category.id_comp]
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homotopyHom_eqToHom (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H G) he (by
    change (G ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst Y (Δ[1] : SSet.{u}) ≫ (G ≫ 𝟙 X)
    simpa only [Category.comp_id] using hG)]
  simp only [retractionCounit, eqToHom_map, eqToHom_trans, eqToHom_refl]
  change 𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (G ≫ 𝟙 X))) = _
  rfl

/-- 指定された厳密な恒等とホモトピーを単位・余単位に持つ実随伴。 -/
def adjunctionOfRetractionHomotopy : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.adjunctionOfFunctorHomTriangles (retractionHomotopyUnit H) (retractionCounit h)
    (retractionHomotopy_leftTriangle h H hF) (retractionHomotopy_rightTriangle h H hG)

end SerrePositivity.KST.LocalizingInvariants
