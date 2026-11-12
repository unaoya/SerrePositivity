module

public import SerrePositivity.KST.LocalizingInvariants.LocalizationUniqueness
public import SerrePositivity.KST.LocalizingInvariants.FunctorHomWhiskering
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.AdjunctionHomTriangles

/-!
概要：右関手が局所化を経由する実随伴を、同じ右関手を持つ商上の実随伴へ下ろす。
方針：前合成の充満忠実性で余単位を持ち上げ、元の三角恒等式を保存・反映する。
規約：三角恒等式を追加仮定にしない。使われ方：局所化が始対象・終対象を保つ証明。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {X Y Z : SSet.{u}} [Quasicategory X] [Quasicategory Y] [Quasicategory Z]
  (F : X ⟶ Y) (L : Y ⟶ Z) (H : Z ⟶ X) (W : Set (Y _⦋1⦌))
  (hL : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization L W) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F (L ≫ H))

def localizationAdjunctionCounit : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (H ≫ (F ≫ L)) (𝟙 Z) :=
  (localizationPre_fullyFaithful L W hL).toHoFullyFaithful.preimage (homPost L a.counitHom)

lemma localizationAdjunctionCounit_pre :
    homPre L (localizationAdjunctionCounit F L H W hL a) = homPost L a.counitHom :=
  (localizationPre_fullyFaithful L W hL).toHoFullyFaithful.map_preimage _

lemma localizationAdjunction_leftTriangle (ε : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (H ≫ (F ≫ L)) (𝟙 Z))
    (hε : homPre L ε = homPost L a.counitHom) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitLeftZigzag (F := F ≫ L) (G := H) a.unitHom ε =
        𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (F ≫ L))) := by
  change homPost (F := 𝟙 X) (G := F ≫ (L ≫ H)) (F ≫ L) a.unitHom ≫
    homPre (F := H ≫ (F ≫ L)) (G := 𝟙 Z) (F ≫ L) ε = _
  rw [homPost_comp F L a.unitHom,
    homPre_comp F L ε, hε, homPre_post,
    ← homPost_homComp]
  exact (congrArg (homPost L) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.adjunction_leftTriangleHom a)).trans (homPost_id L F)

include hL in
lemma localizationAdjunction_rightTriangle (ε : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (H ≫ (F ≫ L)) (𝟙 Z))
    (hε : homPre L ε = homPost L a.counitHom) :
    homPre (F := 𝟙 X) (G := F ≫ (L ≫ H)) H a.unitHom ≫
      homPost (F := H ≫ (F ≫ L)) (G := 𝟙 Z) H ε =
        𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H)) := by
  apply ((localizationPre_fullyFaithful (Y := X) L W hL).homotopyCategoryMap_bijective
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H)).injective
  change homPre L (homPre (F := 𝟙 X) (G := F ≫ (L ≫ H)) H a.unitHom ≫
    homPost (F := H ≫ (F ≫ L)) (G := 𝟙 Z) H ε) = homPre L (𝟙 _)
  rw [homPre_homComp, homPre_id, ← homPre_comp, homPre_post,
    hε, ← homPost_comp]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.adjunction_rightTriangleHom a

def localizationAdjunctionDescent : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (F ≫ L) H :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.adjunctionOfFunctorHomTriangles (F := F ≫ L) (G := H) a.unitHom
    (localizationAdjunctionCounit F L H W hL a)
    (localizationAdjunction_leftTriangle F L H a _
      (localizationAdjunctionCounit_pre F L H W hL a))
    (localizationAdjunction_rightTriangle F L H W hL a _
      (localizationAdjunctionCounit_pre F L H W hL a))

end SerrePositivity.KST.LocalizingInvariants
