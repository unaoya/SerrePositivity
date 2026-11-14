module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorIsoPrecompIdentity
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.Resolutions.ResolutionProjectionComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.Resolutions.ResolutionSourceComparisonNormalization
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerUnit
/-!
概要：元の指定分解変更比較を、同じ実二経路の前合成比較と入力変換へ同定する。
方針：恒等入力と二段前合成則を保ち、元の指定射の共役式を回収する。
規約：同値の逆と比較を選び直さない。使われ方：元の導来射作用との照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet MonoidalClosed
lemma qCatResolutionOutputComparisonIso_precomp_id_heq
    {X Y A T : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    [Quasicategory A] [Quasicategory T]
    (Q : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X A) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence Y A)
    (H : X ⟶ Y) (RX : X ⟶ T) (RY : Y ⟶ T)
    (hs : H ≫ S.hom = Q.hom) (hr : H ≫ RY = RX) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionOutputComparisonIso Q S H RX RY hs hr)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionOutputPrecompIso Q S (𝟙 A) H RX RY
        (by simpa only [Category.comp_id] using hs) hr) := by
  subst RX
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionOutputComparisonIso, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionOutputPrecompIso,
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_id, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_precomp_id, Eq.mp, Eq.mpr]
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
