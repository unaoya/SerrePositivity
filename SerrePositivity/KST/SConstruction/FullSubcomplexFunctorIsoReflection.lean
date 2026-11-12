module
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FullSubcomplexFunctorFaithful

/-! # 全部分複体の包含による関手同型の反映
概要：包含後に coherent に同型な二つの関手は全部分複体の内部でも関手同型を持つ。
方針：h Fun の充満忠実な包含で同型の逆像を取る。
規約：始域の quasicategory 性は不要。使われ方：支持部分圏の制限と延長の逆同値。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 全部分複体の包含後の関手同型を内部の関手同型に戻す。 -/
def functorIsoOfFullSubcomplexPostcomp {K C : SSet.{u}} [Quasicategory C]
    (P : C _⦋0⦌ → Prop) {f g : K ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices C P : SSet.{u})}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (f ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices C P).ι)
      (g ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices C P).ι)) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g :=
  (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.fullSubcomplexFunctorInclusionHoFullyFaithful K C P).preimageIso e

end SerrePositivity.KST.SConstruction
