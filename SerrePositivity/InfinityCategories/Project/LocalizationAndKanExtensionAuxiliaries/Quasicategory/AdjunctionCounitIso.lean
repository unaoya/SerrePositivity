module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.Adjunction

/-!
概要：随伴の余単位の可逆性を h Fun の表示から実二胞体へ戻す。
方針：逆二胞体を Hom 表示の逆で作り、忠実性で逆恒等式を反映する。
規約：点ごとの可逆性は入力しない。使われ方：K-8 の反射射影の可逆余単位。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory
open _root_.SerrePositivity.KST.LocalizingInvariants

local instance counitIsoCategory (X Y : SSet.QCat.{u}) : Category.{u} (X ⟶ Y) :=
  SSet.QCat.bicategory.homCategory X Y

lemma counit_isIso_of_counitHom {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G) [IsIso a.counitHom] :
    IsIso a.counit := by
  let β := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (𝟙 Y) (G ≫ F)).symm (inv a.counitHom)
  have hβ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatHomFunctor Y Y).map β = inv a.counitHom :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (𝟙 Y) (G ≫ F)).apply_symm_apply _
  refine ⟨⟨β, ?_, ?_⟩⟩
  · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatHomFunctor Y Y).map_injective
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id, hβ]
    exact IsIso.hom_inv_id a.counitHom
  · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatHomFunctor Y Y).map_injective
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id, hβ]
    exact IsIso.inv_hom_id a.counitHom

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
