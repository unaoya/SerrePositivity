module

public import SerrePositivity.EInfinity.FrameHom.FrameArrowAugmentationLimits
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CosliceHomotopyRealization
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.Shapes

/-!
# 元の frame の全矢から実右 Kan 形状への比較

概要：同じ augmentation の逆と元の右脚を、一つの全変換として coslice に実現する。
方針：元の関手同型と右脚の円柱の h Fun 類を合成し、全区間を持ち上げる。
規約：元の qX・始域射影・全右脚を保持する。left cofinal 性は別工程。
使われ方：source frame の実局所極限を右 Kan 図式へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.FrameHom.FrameArrows
open CategoryTheory Opposite Limits SerrePositivity.InfinityCategories
open SerrePositivity.SimplicialModel
open scoped Simplicial
variable {I C : Type u} [Category.{u} I] [Category.{u} C]
  (A : I ⥤ C) {X : C} (p : A ⟶ (Functor.const I).obj X)
  {E : SSet.{u}} [SSet.Quasicategory E] (q : nerve C ⟶ E)
  (hp : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((nerve.edgeMk (p.app i)).map q).toTruncated)

def totalAugmentation : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FrameArrowCategory.degree A ⋙ A ⟶ (Functor.const (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FrameArrowCategory.Total A)).obj X where
  app s := p.app s.left
  naturality _ _ f := p.naturality f.left

def rightKanComparisonCell :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (SSet.const (X := nerve (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FrameArrowCategory.Total A))
      (q.app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X))) (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FrameArrowCategory.target A) ≫ q) :=
  (augmentationFunctorIso (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FrameArrowCategory.degree A ⋙ A) (totalAugmentation A p) q
    (fun s => hp s.left)).inv ≫
      SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (HomotopyClasses.postHomotopy q
          (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FrameArrowCategory.rightLeg A))))

def rightKanComparisonHomotopy :
    SSet.Homotopy (SSet.const (X := nerve (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FrameArrowCategory.Total A))
      (q.app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X))) (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FrameArrowCategory.target A) ≫ q) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy (rightKanComparisonCell A p q hp)

lemma rightKanComparisonHomotopy_hom :
    SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (rightKanComparisonHomotopy A p q hp)) =
        rightKanComparisonCell A p q hp :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy_hom _

def rightKanCosliceRealization :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.CosliceHomotopyRealization (q.app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X))
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FrameArrowCategory.target A) ≫ q) (rightKanComparisonHomotopy A p q hp) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cosliceHomotopyRealization_nonempty _ _ _).some

def rightKanMap : nerve (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FrameArrowCategory.Total A) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanShape q (q.app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X)) :=
  pullback.lift (rightKanCosliceRealization A p q hp).diagram (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FrameArrowCategory.target A))
    (rightKanCosliceRealization A p q hp).projection

lemma rightKanMap_projection : rightKanMap A p q hp ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanProjection q (q.app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X)) = nerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FrameArrowCategory.target A) :=
  pullback.lift_snd _ _ _

lemma rightKanMap_coslice : rightKanMap A p q hp ≫ pullback.fst _ _ =
    (rightKanCosliceRealization A p q hp).diagram := pullback.lift_fst _ _ _

lemma rightKanMap_diagram {Z : SSet.{u}} (F : nerve C ⟶ Z) :
    rightKanMap A p q hp ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram q F (q.app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X)) =
      nerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FrameArrowCategory.target A) ≫ F := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram, ← Category.assoc, rightKanMap_projection]

end SerrePositivity.EInfinity.FrameHom.FrameArrows
