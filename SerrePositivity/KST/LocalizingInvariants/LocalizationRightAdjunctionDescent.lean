module

public import SerrePositivity.KST.LocalizingInvariants.LocalizationAdjunctionDescent

/-!
概要：左関手が局所化を経由する実随伴を、商からの同じ左関手の実随伴へ下ろす。
方針：前合成の充満忠実性で単位を持ち上げ、元の三角恒等式を保存・反映する。
規約：両三角を全関手上で証明。使われ方：局所化の終対象保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {X Y Z : SSet.{u}} [Quasicategory X] [Quasicategory Y] [Quasicategory Z]
  (F : X ⟶ Y) (L : Y ⟶ Z) (H : Z ⟶ X) (W : Set (Y _⦋1⦌))
  (hL : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization L W) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (L ≫ H) F)

def localizationRightAdjunctionUnit : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 Z) (H ≫ (F ≫ L)) :=
  (localizationPre_fullyFaithful L W hL).toHoFullyFaithful.preimage (homPost L a.unitHom)

lemma localizationRightAdjunctionUnit_pre :
    homPre L (localizationRightAdjunctionUnit F L H W hL a) = homPost L a.unitHom :=
  (localizationPre_fullyFaithful L W hL).toHoFullyFaithful.map_preimage _

include hL in
lemma localizationRightAdjunction_leftTriangle (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 Z) (H ≫ (F ≫ L)))
    (hη : homPre L η = homPost L a.unitHom) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitLeftZigzag (F := H) (G := F ≫ L) η a.counitHom =
      𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H)) := by
  apply ((localizationPre_fullyFaithful (Y := X) L W hL).homotopyCategoryMap_bijective
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H)).injective
  change homPre L (homPost H η ≫
    homPre (F := F ≫ (L ≫ H)) (G := 𝟙 X) H a.counitHom) = homPre L (𝟙 _)
  rw [homPre_homComp, homPre_id, homPre_post, hη, ← homPost_comp, ← homPre_comp]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.adjunction_leftTriangleHom a

lemma localizationRightAdjunction_rightTriangle (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 Z) (H ≫ (F ≫ L)))
    (hη : homPre L η = homPost L a.unitHom) :
    homPre (F ≫ L) η ≫ homPost (F := F ≫ (L ≫ H)) (G := 𝟙 X) (F ≫ L) a.counitHom =
      𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (F ≫ L))) := by
  rw [homPre_comp F L η, hη, homPre_post, homPost_comp, ← homPost_homComp]
  exact (congrArg (homPost L) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.adjunction_rightTriangleHom a)).trans (homPost_id L F)

def localizationRightAdjunctionDescent : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction H (F ≫ L) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.adjunctionOfFunctorHomTriangles (F := H) (G := F ≫ L)
    (localizationRightAdjunctionUnit F L H W hL a) a.counitHom
    (localizationRightAdjunction_leftTriangle F L H W hL a _
      (localizationRightAdjunctionUnit_pre F L H W hL a))
    (localizationRightAdjunction_rightTriangle F L H a _
      (localizationRightAdjunctionUnit_pre F L H W hL a))

end SerrePositivity.KST.LocalizingInvariants
