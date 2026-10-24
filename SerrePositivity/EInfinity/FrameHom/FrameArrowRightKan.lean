module

public import SerrePositivity.EInfinity.FrameHom.FrameArrowAugmentationLimits
public import SerrePositivity.InfinityCategories.Derived.CosliceHomotopyRealization
public import SerrePositivity.InfinityCategories.F1B.KanExtension.Shapes

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
  (hp : ∀ i, IsInvertibleEdge ((nerve.edgeMk (p.app i)).map q).toTruncated)

def totalAugmentation : degree A ⋙ A ⟶ (Functor.const (Total A)).obj X where
  app s := p.app s.left
  naturality _ _ f := p.naturality f.left

def rightKanComparisonCell :
    FunctorHom (SSet.const (X := nerve (Total A))
      (q.app (op ⦋0⦌) (nerveVertex X))) (nerveMap (target A) ≫ q) :=
  (augmentationFunctorIso (degree A ⋙ A) (totalAugmentation A p) q
    (fun s => hp s.left)).inv ≫
      SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (HomotopyClasses.postHomotopy q
          (SerrePositivity.InfinityCategories.F1B.nerveNatTransHomotopy (rightLeg A))))

def rightKanComparisonHomotopy :
    SSet.Homotopy (SSet.const (X := nerve (Total A))
      (q.app (op ⦋0⦌) (nerveVertex X))) (nerveMap (target A) ≫ q) :=
  functorHomHomotopy (rightKanComparisonCell A p q hp)

lemma rightKanComparisonHomotopy_hom :
    SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (rightKanComparisonHomotopy A p q hp)) =
        rightKanComparisonCell A p q hp :=
  functorHomHomotopy_hom _

def rightKanCosliceRealization :
    CosliceHomotopyRealization (q.app (op ⦋0⦌) (nerveVertex X))
      (nerveMap (target A) ≫ q) (rightKanComparisonHomotopy A p q hp) :=
  (cosliceHomotopyRealization_nonempty _ _ _).some

def rightKanMap : nerve (Total A) ⟶
    rightKanShape q (q.app (op ⦋0⦌) (nerveVertex X)) :=
  pullback.lift (rightKanCosliceRealization A p q hp).diagram (nerveMap (target A))
    (rightKanCosliceRealization A p q hp).projection

lemma rightKanMap_projection : rightKanMap A p q hp ≫
    rightKanProjection q (q.app (op ⦋0⦌) (nerveVertex X)) = nerveMap (target A) :=
  pullback.lift_snd _ _ _

lemma rightKanMap_coslice : rightKanMap A p q hp ≫ pullback.fst _ _ =
    (rightKanCosliceRealization A p q hp).diagram := pullback.lift_fst _ _ _

lemma rightKanMap_diagram {Z : SSet.{u}} (F : nerve C ⟶ Z) :
    rightKanMap A p q hp ≫ rightKanDiagram q F (q.app (op ⦋0⦌) (nerveVertex X)) =
      nerveMap (target A) ≫ F := by
  rw [rightKanDiagram, ← Category.assoc, rightKanMap_projection]

end SerrePositivity.EInfinity.FrameHom.FrameArrows
