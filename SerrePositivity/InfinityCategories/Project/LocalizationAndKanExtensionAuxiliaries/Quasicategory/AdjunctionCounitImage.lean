module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveUnitInvertible

/-!
概要：可逆な単位を持つ随伴の余単位は、右随伴で写すと可逆になる。
方針：右三角恒等式から単位の whisker と結合子を相殺し、h Fun の表示へ移す。
規約：余単位全体の可逆性は要求しない。使われ方：lax 余単位の第二射影の零 cofiber。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Bicategory MonoidalClosed SSet
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory
open _root_.SerrePositivity.KST.LocalizingInvariants
open _root_.SerrePositivity.InfinityCategories

lemma whiskerRight_counit_isIso_of_unit
    {B : Type u} [Bicategory.{w, v} B] {a b : B} {f : a ⟶ b} {g : b ⟶ a}
    (adj : Bicategory.Adjunction f g) [IsIso adj.unit] : IsIso (adj.counit ▷ g) := by
  have h : (g ◁ adj.unit) ≫ ((α_ g f g).inv ≫ adj.counit ▷ g) =
      (ρ_ g).hom ≫ (λ_ g).inv := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.bicategory_rightZigzag_explicit]
    exact adj.right_triangle
  have : IsIso ((α_ g f g).inv ≫ adj.counit ▷ g) := IsIso.of_isIso_fac_left h
  exact IsIso.of_isIso_comp_left (α_ g f g).inv (adj.counit ▷ g)

lemma whiskerLeft_counit_isIso_of_unit
    {B : Type u} [Bicategory.{w, v} B] {a b : B} {f : a ⟶ b} {g : b ⟶ a}
    (adj : Bicategory.Adjunction f g) [IsIso adj.unit] : IsIso (f ◁ adj.counit) := by
  have h : (adj.unit ▷ f) ≫ ((α_ f g f).hom ≫ f ◁ adj.counit) =
      (λ_ f).hom ≫ (ρ_ f).inv := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.bicategory_leftZigzag_explicit]
    exact adj.left_triangle
  have : IsIso ((α_ f g f).hom ≫ f ◁ adj.counit) := IsIso.of_isIso_fac_left h
  exact IsIso.of_isIso_comp_left (α_ f g f).hom (f ◁ adj.counit)

local instance counitImageHomCategory (A B : SSet.QCat.{u}) : Category.{u} (A ⟶ B) :=
  SSet.QCat.bicategory.homCategory A B

lemma counit_postcompRight_isIso
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G) [IsIso a.unitHom] :
    IsIso ((hoFunctor.map ((ihom Y).map G)).toFunctor.map a.counitHom) := by
  have : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatHomFunctor X X).Full := ⟨fun f => ⟨CatEnrichedOrdinary.Hom.mk f, rfl⟩⟩
  have : IsIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatHomFunctor X X).map a.unit) := inferInstanceAs (IsIso a.unitHom)
  have : IsIso a.unit := isIso_of_reflects_iso a.unit (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatHomFunctor X X)
  have : IsIso (a.counit ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap G) := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.whiskerRight_counit_isIso_of_unit a
  have h : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ (a.counit ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap G)) := by
    change IsIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatHomFunctor Y X).map (a.counit ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap G))
    infer_instance
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCell_whiskerRight a.counit G) ▸ h

lemma counit_precompLeft_isIso
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G) [IsIso a.unitHom] :
    IsIso ((hoFunctor.map ((pre F).app Y)).toFunctor.map a.counitHom) := by
  have : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatHomFunctor X X).Full := ⟨fun f => ⟨CatEnrichedOrdinary.Hom.mk f, rfl⟩⟩
  have : IsIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatHomFunctor X X).map a.unit) := inferInstanceAs (IsIso a.unitHom)
  have : IsIso a.unit := isIso_of_reflects_iso a.unit (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatHomFunctor X X)
  have : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap F ◁ a.counit) := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.whiskerLeft_counit_isIso_of_unit a
  have h : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap F ◁ a.counit)) := by
    change IsIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatHomFunctor X Y).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap F ◁ a.counit))
    infer_instance
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCell_whiskerLeft F a.counit) ▸ h

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.counitImageHomCategory (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.counitImageHomCategory := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.counitImageHomCategory

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.counit_postcompRight_isIso := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.counit_postcompRight_isIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.counit_precompLeft_isIso := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.counit_precompLeft_isIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.whiskerLeft_counit_isIso_of_unit := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.whiskerLeft_counit_isIso_of_unit

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.whiskerRight_counit_isIso_of_unit := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.whiskerRight_counit_isIso_of_unit
