module

public import SerrePositivity.EInfinity.SimplicialLocalization.KanHammockSourceFunctor
public import SerrePositivity.InfinityCategories.F1.Coherent.HomEquivalence
public import SerrePositivity.InfinityCategories.Core.Roof.PinchedEndpointTransport

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
open SerrePositivity.KST.Comparison
open scoped Simplicial
variable (C : RelativeCategory.{u}) (X Y : C.category)

def kanHammockHomLiftIso : exInfinity.obj (colimitGraph C.weakEquivalences X Y) ≅
    SSet.uliftFunctor.{u, u}.obj (SimplicialCategory.sHom
      ((kanHammockSourceFunctor C).obj X) ((kanHammockSourceFunctor C).obj Y)) where
  hom := { app _ := ↾ULift.up, naturality _ _ _ := rfl }
  inv := { app _ := ↾ULift.down, naturality _ _ _ := rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

def kanHammockHomPinchedMap : exInfinity.obj (colimitGraph C.weakEquivalences X Y) ⟶
    pinchedHom ((hammockLocalizationNerveMap C).app (op ⦋0⦌) (nerveVertex X))
      ((hammockLocalizationNerveMap C).app (op ⦋0⦌) (nerveVertex Y)) :=
  (kanHammockHomLiftIso C X Y).hom ≫
    coherentHomComparison ((kanHammockSourceFunctor C).obj X) ((kanHammockSourceFunctor C).obj Y) ≫
      (pinchedEndpointIso (X := kanHammockNerve C)
        (hammockLocalizationNerveMap_vertex C X).symm
        (hammockLocalizationNerveMap_vertex C Y).symm).hom

lemma kanHammockHomPinchedMap_weak :
    IsWeakHomotopyEquivalence (kanHammockHomPinchedMap C X Y) := by
  have h₀ := (isPrecompositionEquivalence_of_iso
    (kanHammockHomLiftIso C X Y)).isWeakHomotopyEquivalence
  have h₁ := (coherentHomComparison_isQCatEquivalence
    ((kanHammockSourceFunctor C).obj X)
    ((kanHammockSourceFunctor C).obj Y)).isWeakHomotopyEquivalence
  have h₂ := (isPrecompositionEquivalence_of_iso
    (pinchedEndpointIso (X := kanHammockNerve C)
      (hammockLocalizationNerveMap_vertex C X).symm
      (hammockLocalizationNerveMap_vertex C Y).symm)).isWeakHomotopyEquivalence
  exact h₀.comp (h₁.comp h₂)

end SerrePositivity.EInfinity.SimplicialLocalization
