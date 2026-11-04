module

public import SerrePositivity.InfinityCategories.F1B.Adjunction.AdjunctionHomTriangles

/-!
概要：h Fun の指定された単位・余単位と三角恒等式から実随伴を構成する。
方針：二胞体の表示全単射で戻し、既存の h Fun による三角判定を適用する。
規約：点ごとの等式に弱めない。使われ方：K-8 の反転した随伴の復元。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Bicategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

local instance homTrianglesCategory (A B : SSet.QCat.{u}) : Category.{u} (A ⟶ B) :=
  SSet.QCat.bicategory.homCategory A B

variable {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
  {F : X ⟶ Y} {G : Y ⟶ X}

def adjunctionOfFunctorHomTriangles (η : FunctorHom (𝟙 X) (F ≫ G))
    (ε : FunctorHom (G ≫ F) (𝟙 Y))
    (hL : unitLeftZigzag η ε = 𝟙 (HomotopyCategory.mk (functorVertex F)))
    (hR : (hoFunctor.map ((pre G).app X)).toFunctor.map η ≫
      (hoFunctor.map ((ihom Y).map G)).toFunctor.map ε =
        𝟙 (HomotopyCategory.mk (functorVertex G))) : QCatAdjunction F G := by
  refine QCatAdjunction.mkOfHomTriangles ((qcatCellEquiv _ _).symm η)
    ((qcatCellEquiv _ _).symm ε) ?_ ?_
  · rw [qcatLeftZigzag_hom]
    simp only [Strict.leftUnitor_eqToIso, Strict.rightUnitor_eqToIso, eqToIso.hom,
      eqToIso.inv, eqToHom_refl, Category.id_comp]
    exact hL.trans ((qcatHomFunctor X Y).map_id (qcatMap F)).symm
  · rw [qcatRightZigzag_hom]
    simp only [Strict.leftUnitor_eqToIso, Strict.rightUnitor_eqToIso, eqToIso.hom,
      eqToIso.inv, eqToHom_refl, Category.id_comp]
    exact hR.trans ((qcatHomFunctor Y X).map_id (qcatMap G)).symm

lemma adjunctionOfFunctorHomTriangles_counit (η : FunctorHom (𝟙 X) (F ≫ G))
    (ε : FunctorHom (G ≫ F) (𝟙 Y))
    (hL : unitLeftZigzag η ε = 𝟙 (HomotopyCategory.mk (functorVertex F)))
    (hR : (hoFunctor.map ((pre G).app X)).toFunctor.map η ≫
      (hoFunctor.map ((ihom Y).map G)).toFunctor.map ε =
        𝟙 (HomotopyCategory.mk (functorVertex G))) :
    (adjunctionOfFunctorHomTriangles η ε hL hR).counitHom = ε :=
  (qcatCellEquiv (G ≫ F) (𝟙 Y)).apply_symm_apply ε

end SerrePositivity.KST.LocalizingInvariants
