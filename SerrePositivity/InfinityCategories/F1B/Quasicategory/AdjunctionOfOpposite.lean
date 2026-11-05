module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.F1B.Quasicategory.OppositeAdjunction
public import SerrePositivity.InfinityCategories.F1B.Quasicategory.OppositeFunctorIso

/-!
概要：反転した二関手の実随伴から元の二関手の実随伴を復元する。
方針：反転 Hom 全単射の逆で単位・余単位を戻し、三角恒等式を単射性で反映する。
規約：二重反転した対象への置換は使わない。使われ方：K-8 の C 側の随伴。
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
  {F : X ⟶ Y} {G : Y ⟶ X}
  (a : QCatAdjunction (SSet.opFunctor.map G) (SSet.opFunctor.map F))

def restoredUnit : FunctorHom (𝟙 X) (F ≫ G) :=
  (SerrePositivity.InfinityCategories.F1B.functorOppositeHomEquiv (𝟙 X) (F ≫ G)).symm a.counitHom

def restoredCounit : FunctorHom (G ≫ F) (𝟙 Y) :=
  (SerrePositivity.InfinityCategories.F1B.functorOppositeHomEquiv (G ≫ F) (𝟙 Y)).symm a.unitHom

lemma restored_leftTriangle : unitLeftZigzag (restoredUnit a) (restoredCounit a) =
    𝟙 (HomotopyCategory.mk (functorVertex F)) := by
  apply (SerrePositivity.InfinityCategories.F1B.functorOppositeHomEquiv F F).injective
  unfold unitLeftZigzag
  erw [SerrePositivity.InfinityCategories.F1B.functorOppositeHomEquiv_comp (F := F) (G := F ≫ G ≫ F) (H := F),
    oppositeFunctorHom_postcomp F (F := 𝟙 X) (G := F ≫ G) (restoredUnit a),
    SerrePositivity.InfinityCategories.F1B.functorOppositeHomEquiv_precomp F (F := G ≫ F) (G := 𝟙 Y) (restoredCounit a),
    oppositeFunctorHom_id]
  simp only [restoredUnit, restoredCounit, Equiv.apply_symm_apply]
  exact SerrePositivity.InfinityCategories.F1B.adjunction_rightTriangleHom a

lemma restored_rightTriangle :
    (hoFunctor.map ((pre G).app X)).toFunctor.map (restoredUnit a) ≫
      (hoFunctor.map ((ihom Y).map G)).toFunctor.map (restoredCounit a) =
        𝟙 (HomotopyCategory.mk (functorVertex G)) := by
  apply (SerrePositivity.InfinityCategories.F1B.functorOppositeHomEquiv G G).injective
  erw [SerrePositivity.InfinityCategories.F1B.functorOppositeHomEquiv_comp (F := G) (G := G ≫ F ≫ G) (H := G),
    SerrePositivity.InfinityCategories.F1B.functorOppositeHomEquiv_precomp G (F := 𝟙 X) (G := F ≫ G) (restoredUnit a),
    oppositeFunctorHom_postcomp G (F := G ≫ F) (G := 𝟙 Y) (restoredCounit a),
    oppositeFunctorHom_id]
  simp only [restoredUnit, restoredCounit, Equiv.apply_symm_apply]
  exact SerrePositivity.InfinityCategories.F1B.adjunction_leftTriangleHom a

def adjunctionOfOpposite : QCatAdjunction F G :=
  adjunctionOfFunctorHomTriangles (restoredUnit a) (restoredCounit a)
    (restored_leftTriangle a) (restored_rightTriangle a)

lemma adjunctionOfOpposite_counit : (adjunctionOfOpposite a).counitHom = restoredCounit a :=
  adjunctionOfFunctorHomTriangles_counit _ _ _ _

instance restoredCounit_isIso [IsIso a.unitHom] : IsIso (restoredCounit a) :=
  inferInstanceAs (IsIso (restoredFunctorIso (F := G ≫ F) (G := 𝟙 Y) (asIso a.unitHom)).hom)

end SerrePositivity.InfinityCategories.F1B.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.adjunctionOfOpposite (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.adjunctionOfOpposite := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.adjunctionOfOpposite

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.adjunctionOfOpposite_counit := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.adjunctionOfOpposite_counit

@[deprecated _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.restoredCounit (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.restoredCounit := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.restoredCounit

@[deprecated _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.restoredCounit_isIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.restoredCounit_isIso := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.restoredCounit_isIso

@[deprecated _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.restoredUnit (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.restoredUnit := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.restoredUnit

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.restored_leftTriangle := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.restored_leftTriangle

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.restored_rightTriangle := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.restored_rightTriangle

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.restoredCounit.eq_1 := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.restoredCounit.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.restoredUnit.eq_1 := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.restoredUnit.eq_1
