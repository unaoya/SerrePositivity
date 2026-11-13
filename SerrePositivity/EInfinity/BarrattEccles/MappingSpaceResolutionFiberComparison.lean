module

public import SerrePositivity.EInfinity.BarrattEccles.MappingResolutionRightInvariance
public import SerrePositivity.EInfinity.BarrattEccles.MappingSpaceBarInclusion
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FunctorComparison.NerveULiftHom

/-!
# 元の共通添字から分解の固定 fiber と全図式への比較

概要：元の Map^h の全単体の共通始域を、同じ置換の固定 fiber と全図式へ送る。
方針：Hom と対象の二つの宇宙比較を同じ ULift nerve で揃え、明示的な表示同値を合成。
規約：元の Map^h・右脚・全単体を変更しない。逆の代表の選択は使わない。
使われ方：元の三本矢への右比較射の同じ元の射での因子分解。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Opposite
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open SerrePositivity.Reedy

namespace SerrePositivity.EInfinity.BarrattEccles

variable (A : Type u) [CommRing A]

/-- 元の Map^h の同じ fibrant 置換の右脚を小圏へ送る。 -/
def mappingSpaceResolutionRightLeg (Y : (operad A).Algebra) :
    AsSmall.{u + 1} (algebraRightSpanBase A Y) :=
  AsSmall.up.obj (mappingFibrantRightLeg A Y)

/-- 元の Map^h の反対要素圏と、同じ右脚の分解の固定 fiber の明示的な同値。 -/
def mappingSpaceResolutionFiberEquivalence (X Y : (operad A).Algebra) :
    AsSmall.{u + 1} (((((mappingSpace A).obj (op X)).obj Y).Elements)ᵒᵖ) ≌
      (mappingSmallResolutionRightDiagram A X Y).obj (mappingSpaceResolutionRightLeg A Y) := by
  let := modelCategory A
  exact FrameHom.CosimplicialHomElements.smallEquivalence.{u + 1, u, u + 1}
    ((cosimplicialResolutionFamily (mappingCofibrantFactorization A)).obj.obj X)
    ((fibrantTarget (mappingFibrantFactorization A)).obj Y)

/-- 元の全単体の共通始域から同じ固定 fiber の nerve への比較。 -/
def mappingSpaceResolutionFiberNerveMap (X Y : (operad A).Algebra) :
    nerve (ULiftHom.{u + 1} (((((mappingSpace A).obj (op X)).obj Y).Elements)ᵒᵖ)) ⟶
      nerve ((mappingSmallResolutionRightDiagram A X Y).obj
        (mappingSpaceResolutionRightLeg A Y)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.NerveULiftHom.iso.{u, 0, u + 1} _).hom ≫
    (FrameHom.NerveAsSmall.iso.{u, 0, u + 1} _).inv ≫
      nerveMap (mappingSpaceResolutionFiberEquivalence A X Y).functor

/-- 全単体で元の同じ中間射を回収する。 -/
lemma mappingSpaceResolutionFiberNerveMap_hom (X Y : (operad A).Algebra)
    (n : SimplexCategoryᵒᵖ)
    (c : (nerve (ULiftHom.{u + 1}
      (((((mappingSpace A).obj (op X)).obj Y).Elements)ᵒᵖ))).obj n)
    (j : Fin (n.unop.len + 1)) :
    (((mappingSpaceResolutionFiberNerveMap A X Y).app n c).obj j).hom.down =
      (c.obj j).unop.val := rfl

/-- 同じ共通始域から同じ固定 fiber への射そのものは局所化で可逆。 -/
lemma mappingSpaceResolutionFiberNerveMap_localized_isIso (X Y : (operad A).Algebra) :
    IsIso (AnodyneHomotopy.anodyneQ.map (mappingSpaceResolutionFiberNerveMap A X Y)) := by
  have : IsIso (AnodyneHomotopy.anodyneQ.map
      (nerveMap (mappingSpaceResolutionFiberEquivalence A X Y).functor)) :=
    (FrameHom.NerveEquivalenceImage.imageIso (mappingSpaceResolutionFiberEquivalence A X Y)
      AnodyneHomotopy.anodyneQ (Localization.inverts _ SSet.anodyneExtensions)).isIso_hom
  dsimp only [mappingSpaceResolutionFiberNerveMap]
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  infer_instance

/-- 元の全単体の共通始域から同じ右脚の分解の全図式の nerve への射。 -/
def mappingSpaceResolutionGrothendieckNerveMap (X Y : (operad A).Algebra) :
    nerve (ULiftHom.{u + 1} (((((mappingSpace A).obj (op X)).obj Y).Elements)ᵒᵖ)) ⟶
      nerve (Grothendieck (mappingSmallResolutionRightDiagram A X Y)) :=
  mappingSpaceResolutionFiberNerveMap A X Y ≫
    (FrameHom.Thomason.selfLiftIso _).inv ≫ FrameHom.Thomason.fiberNerveMap
      (mappingSmallResolutionRightDiagram A X Y) (mappingSpaceResolutionRightLeg A Y)

/-- 同じ元の右脚で全図式へ入れる比較射そのものも局所化で可逆。 -/
lemma mappingSpaceResolutionGrothendieckNerveMap_localized_isIso
    (X Y : (operad A).Algebra) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (mappingSpaceResolutionGrothendieckNerveMap A X Y)) := by
  have := mappingSpaceResolutionFiberNerveMap_localized_isIso A X Y
  have := mappingResolutionFiberNerveMap_localized_isIso A X Y (mappingSpaceResolutionRightLeg A Y)
  dsimp only [mappingSpaceResolutionGrothendieckNerveMap]
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  infer_instance

/-- 同じ共通始域から、全左脚・全右脚の小さい全図式へ入れる元の比較。 -/
def mappingSpaceSmallSpanGrothendieckNerveMap (X Y : (operad A).Algebra) :
    nerve (ULiftHom.{u + 1} (((((mappingSpace A).obj (op X)).obj Y).Elements)ᵒᵖ)) ⟶
      nerve (Grothendieck (mappingSmallSpanRightDiagram A X Y)) :=
  mappingSpaceResolutionGrothendieckNerveMap A X Y ≫
    nerveMap (mappingFixedRightGrothendieckComparison A X Y)

/-- 全単体で、全左脚への元の比較の後も元の同じ中間射を保持。 -/
lemma mappingSpaceSmallSpanGrothendieckNerveMap_hom (X Y : (operad A).Algebra)
    (n : SimplexCategoryᵒᵖ)
    (c : (nerve (ULiftHom.{u + 1}
      (((((mappingSpace A).obj (op X)).obj Y).Elements)ᵒᵖ))).obj n)
    (j : Fin (n.unop.len + 1)) :
    (((mappingSpaceSmallSpanGrothendieckNerveMap A X Y).app n c).obj j).fiber.hom.down =
      (c.obj j).unop.val := rfl

/-- 同じ元の全左脚・全右脚の小さい全図式への比較そのものも局所化で可逆。 -/
lemma mappingSpaceSmallSpanGrothendieckNerveMap_localized_isIso
    (X Y : (operad A).Algebra) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (mappingSpaceSmallSpanGrothendieckNerveMap A X Y)) := by
  have := mappingSpaceResolutionGrothendieckNerveMap_localized_isIso A X Y
  have := mappingFixedRightGrothendieckComparison_localized_isIso A X Y
  dsimp only [mappingSpaceSmallSpanGrothendieckNerveMap]
  rw [CategoryTheory.Functor.map_comp]
  infer_instance

end SerrePositivity.EInfinity.BarrattEccles
