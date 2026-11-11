module

public import SerrePositivity.EInfinity.SimplicialLocalization.KanHammockSourceFunctor
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomEquivalence
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.PinchedEndpointTransport

/-!
# 元の Kan hammock Hom から同じ局所化頂点の pinched Hom への弱比較

概要：元の Ex∞ hammock Hom を、同じ qX・qY の実写像空間へ送る。
方針：Hom の自明な宇宙持ち上げを全単体で往復し、元の coherent 比較を使う。
規約：元の enriched Hom・元の Ex∞・実際の q の頂点を保持する。
使われ方：元の source frame の弱な基準射を実屋根の Hom 比較へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory Opposite Hammock SerrePositivity.InfinityCategories

open scoped Simplicial
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category)

def kanHammockHomLiftIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph C.weakEquivalences X Y) ≅
    SSet.uliftFunctor.{u, u}.obj (SimplicialCategory.sHom
      ((kanHammockSourceFunctor C).obj X) ((kanHammockSourceFunctor C).obj Y)) where
  hom := { app _ := ↾ULift.up, naturality _ _ _ := rfl }
  inv := { app _ := ↾ULift.down, naturality _ _ _ := rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

def kanHammockHomPinchedMap : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph C.weakEquivalences X Y) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom ((hammockLocalizationNerveMap C).app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X))
      ((hammockLocalizationNerveMap C).app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y)) :=
  (kanHammockHomLiftIso C X Y).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison ((kanHammockSourceFunctor C).obj X) ((kanHammockSourceFunctor C).obj Y) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.pinchedEndpointIso (X := kanHammockNerve C)
        (hammockLocalizationNerveMap_vertex C X).symm
        (hammockLocalizationNerveMap_vertex C Y).symm).hom

lemma kanHammockHomPinchedMap_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (kanHammockHomPinchedMap C X Y) := by
  have h₀ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (kanHammockHomLiftIso C X Y)).isWeakHomotopyEquivalence
  have h₁ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison_isQCatEquivalence
    ((kanHammockSourceFunctor C).obj X)
    ((kanHammockSourceFunctor C).obj Y)).isWeakHomotopyEquivalence
  have h₂ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.pinchedEndpointIso (X := kanHammockNerve C)
      (hammockLocalizationNerveMap_vertex C X).symm
      (hammockLocalizationNerveMap_vertex C Y).symm)).isWeakHomotopyEquivalence
  exact h₀.comp (h₁.comp h₂)

end SerrePositivity.EInfinity.SimplicialLocalization
