module

public import SerrePositivity.EInfinity.FrameHom.FrameArrowAugmentationLimits
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.CosliceInitialRealization
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.Shapes

/-!
# 同じ frame augmentation の逆から実右 Kan 形状への比較

概要：元の全 augmentation を同時に反転し、同じ頂点からの coslice 図式へ実現する。
方針：一つの全関手同型の逆を実ホモトピーへ戻し、同じ全底で持ち上げる。
規約：元の qX・次数射影・全区間を保持する。cofinal 性は別に証明する。
使われ方：実屋根比較を用いる source frame の右 Kan 計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.FrameHom.FrameArrows
open CategoryTheory Limits Opposite SerrePositivity.InfinityCategories
open scoped Simplicial
variable {I C : Type u} [Category.{u} I] [Category.{u} C]
  (A : I ⥤ C) {X : C} (p : A ⟶ (Functor.const I).obj X)
  {E : SSet.{u}} [SSet.Quasicategory E] (q : nerve C ⟶ E)
  (hp : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((nerve.edgeMk (p.app i)).map q).toTruncated)

def frameRightKanHomotopy : SSet.Homotopy
    (SSet.const (X := nerve I) (q.app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X))) (nerveMap A ≫ q) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.simplicialHomotopy (augmentationFunctorIso A p q hp).symm

def frameRightKanCosliceRealization :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.CosliceHomotopyRealization (q.app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X)) (nerveMap A ≫ q)
      (frameRightKanHomotopy A p q hp) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cosliceHomotopyRealization_nonempty _ _ _).some

def frameRightKanMap : nerve I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanShape q (q.app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X)) :=
  pullback.lift (frameRightKanCosliceRealization A p q hp).diagram (nerveMap A)
    (frameRightKanCosliceRealization A p q hp).projection

lemma frameRightKanMap_projection : frameRightKanMap A p q hp ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanProjection q (q.app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X)) = nerveMap A :=
  pullback.lift_snd _ _ _

lemma frameRightKanMap_coslice : frameRightKanMap A p q hp ≫ pullback.fst _ _ =
    (frameRightKanCosliceRealization A p q hp).diagram := pullback.lift_fst _ _ _

lemma frameRightKanMap_coslice_initial (i : (nerve I) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex ((frameRightKanMap A p q hp ≫ pullback.fst _ _).app (op ⦋0⦌) i) := by
  rw [frameRightKanMap_coslice]
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.CosliceHomotopyRealization.isInitialVertex (frameRightKanCosliceRealization A p q hp)
  intro j
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.simplicialHomotopyOfFunctorEdge_vertex_isInvertible
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge (augmentationFunctorIso A p q hp).symm)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge_isInvertible (augmentationFunctorIso A p q hp).symm) j

lemma frameRightKanMap_diagram {Z : SSet.{u}} (F : nerve C ⟶ Z) :
    frameRightKanMap A p q hp ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram q F (q.app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X)) =
      nerveMap A ≫ F := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram, ← Category.assoc, frameRightKanMap_projection]

end SerrePositivity.EInfinity.FrameHom.FrameArrows
