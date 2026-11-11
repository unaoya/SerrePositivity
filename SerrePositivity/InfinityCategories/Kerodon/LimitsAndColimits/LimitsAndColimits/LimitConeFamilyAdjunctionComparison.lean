module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ConeFamilyHomUniversal
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ConstantObjectNaturality
public import Mathlib.CategoryTheory.Yoneda

/-!
概要：全極限錐族の頂点と、図式族に極限関手を適用した全関手を同型にする。
方針：指定余単位の全 Hom 普遍性と随伴の自然性から、同じ adjunct の可逆性を示す。
規約：頂点ごとの独立な同型で代用しない。
使われ方：μ-small な極限錐族の filtered 余極限保存。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：全極限錐族の指定 adjunct は全関手圏内で可逆。
方針：任意の全始域からの Hom 上で、随伴と錐の普遍性の全単射を自然性で結合する。
規約：パラメータ A は quasicategory とする。
使われ方：全錐族の頂点と極限関手の比較同型。 -/
lemma coneFamilyAdjunctHom_isIso {A K X : SSet.{u}} [Quasicategory A] [Quasicategory X]
    {R : (ihom K).obj X ⟶ X} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap K X) R)
    (s : A ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join Δ[0] K)).obj X)
    (hs : ∀ x : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexCone (s.app (Opposite.op ⦋0⦌) x))) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coneFamilyAdjunctHom a s) := by
  apply isIso_of_yoneda_map_bijective
  intro T
  obtain ⟨v, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective T
  obtain ⟨V, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A X).surjective v
  let L := s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] K))
  let U := s ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] K)).app X
  have h := (a.homEquiv V U).bijective.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coneFamilyCounitHom_bijective s hs V)
  have heq :
      (a.homEquiv V U) ∘ (fun α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom V L ↦
        (hoFunctor.map ((ihom A).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap K X))).toFunctor.map α ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coneFunctorCounitHom s) =
      (fun α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom V L ↦ α ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coneFamilyAdjunctHom a s) := by
    funext α
    exact a.homEquiv_comp_left L V U α (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coneFunctorCounitHom s)
  rw [heq] at h
  exact h

/-- 概要：全極限錐族の頂点関手は、元の図式族に指定した右随伴を適用した関手と同型。
方針：元の錐の余単位の adjunct を可逆射として束縛する。
規約：全パラメータ上の一つの FunctorIso を返す。
使われ方：小極限と filtered 余極限の交換の同じ全余錐への適用。 -/
def limitConeFamily_apexIso_of_constantAdjunction {A K X : SSet.{u}}
    [Quasicategory A] [Quasicategory X]
    {R : (ihom K).obj X ⟶ X} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap K X) R)
    (s : A ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join Δ[0] K)).obj X)
    (hs : ∀ x : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexCone (s.app (Opposite.op ⦋0⦌) x))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] K)))
      ((s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X) ≫ R) := by
  have := coneFamilyAdjunctHom_isIso a s hs
  exact asIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coneFamilyAdjunctHom a s)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
