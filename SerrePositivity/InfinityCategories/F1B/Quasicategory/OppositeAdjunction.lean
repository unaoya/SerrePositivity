module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.F1B.Quasicategory.OppositeFunctorHom
public import SerrePositivity.InfinityCategories.F1B.Quasicategory.AdjunctionHomTriangles

/-!
概要：quasicategory の実随伴を反転して、左右を交換した実随伴を得る。
方針：二胞体の反転全単射を単位・余単位へ適用し、両三角恒等式を反転する。
規約：反転後も元の全関手上の自然変換を保持する。使われ方：K-8 の C 側の随伴。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.F1B
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.F1B.Quasicategory
open SerrePositivity.KST.LocalizingInvariants

variable {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
  {F : X ⟶ Y} {G : Y ⟶ X} (a : QCatAdjunction F G)

def oppositeUnit : FunctorHom (𝟙 Y.op) (SSet.opFunctor.map G ≫ SSet.opFunctor.map F) :=
  by
    have h := SerrePositivity.InfinityCategories.F1B.functorOppositeHomEquiv (G ≫ F) (𝟙 Y) a.counitHom
    simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using h

def oppositeCounit : FunctorHom (SSet.opFunctor.map F ≫ SSet.opFunctor.map G) (𝟙 X.op) :=
  by
    have h := SerrePositivity.InfinityCategories.F1B.functorOppositeHomEquiv (𝟙 X) (F ≫ G) a.unitHom
    simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using h

lemma opposite_leftTriangle : unitLeftZigzag (oppositeUnit a) (oppositeCounit a) =
    𝟙 (HomotopyCategory.mk (functorVertex (SSet.opFunctor.map G))) := by
  have h := congrArg (SerrePositivity.InfinityCategories.F1B.functorOppositeHomEquiv G G) (SerrePositivity.InfinityCategories.F1B.adjunction_rightTriangleHom a)
  erw [SerrePositivity.InfinityCategories.F1B.functorOppositeHomEquiv_comp (F := G) (G := G ≫ F ≫ G) (H := G),
    SerrePositivity.InfinityCategories.F1B.functorOppositeHomEquiv_precomp G (F := 𝟙 X) (G := F ≫ G) a.unitHom,
    oppositeFunctorHom_postcomp G (F := G ≫ F) (G := 𝟙 Y) a.counitHom,
    oppositeFunctorHom_id] at h
  exact h

lemma opposite_rightTriangle :
    (hoFunctor.map ((pre (SSet.opFunctor.map F)).app Y.op)).toFunctor.map (oppositeUnit a) ≫
      (hoFunctor.map ((ihom X.op).map (SSet.opFunctor.map F))).toFunctor.map
        (oppositeCounit a) = 𝟙 (HomotopyCategory.mk (functorVertex (SSet.opFunctor.map F))) := by
  have h := congrArg (SerrePositivity.InfinityCategories.F1B.functorOppositeHomEquiv F F) (SerrePositivity.InfinityCategories.F1B.adjunction_leftTriangleHom a)
  unfold unitLeftZigzag at h
  erw [SerrePositivity.InfinityCategories.F1B.functorOppositeHomEquiv_comp (F := F) (G := F ≫ G ≫ F) (H := F),
    oppositeFunctorHom_postcomp F (F := 𝟙 X) (G := F ≫ G) a.unitHom,
    SerrePositivity.InfinityCategories.F1B.functorOppositeHomEquiv_precomp F (F := G ≫ F) (G := 𝟙 Y) a.counitHom,
    oppositeFunctorHom_id] at h
  exact h

def oppositeAdjunction : QCatAdjunction (SSet.opFunctor.map G) (SSet.opFunctor.map F) :=
  adjunctionOfFunctorHomTriangles (oppositeUnit a) (oppositeCounit a)
    (opposite_leftTriangle a) (opposite_rightTriangle a)

end SerrePositivity.InfinityCategories.F1B.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.oppositeAdjunction (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.oppositeAdjunction := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.oppositeAdjunction

@[deprecated _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.oppositeCounit (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.oppositeCounit := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.oppositeCounit

@[deprecated _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.oppositeUnit (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.oppositeUnit := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.oppositeUnit

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.opposite_leftTriangle := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.opposite_leftTriangle

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.opposite_rightTriangle := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.opposite_rightTriangle

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.oppositeCounit._proof_1 := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.oppositeCounit._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.oppositeUnit._proof_1 := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.oppositeUnit._proof_1
