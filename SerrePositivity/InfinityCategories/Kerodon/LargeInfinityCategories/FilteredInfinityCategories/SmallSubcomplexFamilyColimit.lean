module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallSubcomplexCofinalFamily

/-!
概要：小さい部分複体を拡大できる同じ部分族の包含余錐は、元の単体集合の通常の余極限。
方針：包含順の上限の余極限を、部分複体から単体集合への filtered 余極限保存で写す。
規約：同じ元の包含を全脚として使う。cofinal map の存在はここからまだ主張しない。
使われ方：終頂点を持つ小さい部分複体による cofinal poset 構成の被覆図式。

対応節は Kerodon 9.1（Tag 05WY）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories
variable (κ : Cardinal.{u}) (X : SSet.{u}) (P : X.Subcomplex → Prop)

/-- 同じ小さい部分複体の包含順から単体集合への図式。 -/
def smallSubcomplexFamilyDiagram : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallSubcomplexFamily κ X P ⥤ SSet.{u} :=
  (show Monotone (fun A : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallSubcomplexFamily κ X P => A.val) from
    fun _ _ h => h).functor ⋙ Subcomplex.toSSetFunctor

/-- 元の単体集合への同じ包含を全脚とする余錐。 -/
def smallSubcomplexFamilyCocone : Cocone (smallSubcomplexFamilyDiagram κ X P) where
  pt := X
  ι := { app A := A.val.ι }

/-- 同じ拡大可能な部分族の元の包含余錐は通常の余極限。 -/
def smallSubcomplexFamilyCocone_isColimit [Fact κ.IsRegular]
    (hP : ∀ A : X.Subcomplex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ A.toSSet →
      ∃ B : X.Subcomplex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ B.toSSet ∧ P B ∧ A ≤ B) :
    IsColimit (smallSubcomplexFamilyCocone κ X P) := by
  have : IsCardinalFiltered (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallSubcomplexFamily κ X P) κ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.smallSubcomplexFamily_isCardinalFiltered hP
  have := isFiltered_of_isCardinalFiltered (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallSubcomplexFamily κ X P) κ
  exact IsColimit.ofIsoColimit (isColimitOfPreserves Subcomplex.toSSetFunctor
    (CompleteLattice.colimitCocone (show Monotone
      (fun A : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallSubcomplexFamily κ X P => A.val) from fun _ _ h => h).functor).isColimit)
    (Cocone.ext (Subcomplex.eqToIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.iSup_smallSubcomplexFamily hP) ≪≫ Subcomplex.topIso X))

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories
