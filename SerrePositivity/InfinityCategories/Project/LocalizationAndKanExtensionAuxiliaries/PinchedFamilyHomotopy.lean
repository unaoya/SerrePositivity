module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.RightIntervalEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFamilyInvariance
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-!
概要：全パラメータの実 pinched Hom 族を、定値関手間の射と実ホモトピーまで照合する。
方針：区間模型の族の表示と、実 pinched 比較の厳密な左逆・ホモトピー切断を使う。
規約：標的だけを quasicategory とする。使われ方：任意標的の実評価族への回収。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries
/-- 実 pinched Hom の任意二族は、h Fun の射が等しいとき、ちょうどホモトピック。 -/
lemma pinchedFamilyHom_eq_iff_homotopy {K X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} {f g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y} :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace x y) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace x y) ↔
        Nonempty (SSet.Homotopy f g) := by
  constructor
  · intro h
    obtain ⟨r, hr⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_exists_retraction x y
    obtain ⟨H⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom_eq_imp_homotopy h
    refine ⟨{ h := H.h ≫ r, h₀ := ?_, h₁ := ?_, rel := ?_ }⟩
    · change (SSet.ι₀ ≫ H.h) ≫ r = f
      rw [H.h₀, Category.assoc, hr, Category.comp_id]
    · change (SSet.ι₁ ≫ H.h) ≫ r = g
      rw [H.h₁, Category.assoc, hr, Category.comp_id]
    · apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro s
      exact False.elim s.1.property
  · rintro ⟨H⟩
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFamilyHom_eq_of_homotopy
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace x y))
/-- 任意パラメータの定値関手間の射は、実 pinched Hom の一つの族で表示できる。 -/
lemma pinchedFamilyHom_surjective (K X : SSet.{u}) [Quasicategory X] (x y : X _⦋0⦌) :
    Function.Surjective (fun f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y =>
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace x y)) := by
  intro α
  obtain ⟨a, ha⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom_surjective K X x y α
  obtain ⟨b, ⟨H⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_exists_homotopy a
  exact ⟨b, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFamilyHom_eq_of_homotopy H).trans ha⟩
end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries
