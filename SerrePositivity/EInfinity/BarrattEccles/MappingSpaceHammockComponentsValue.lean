module

public import SerrePositivity.EInfinity.BarrattEccles.HammockLocalizationValue
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.UniverseLift.UniverseLiftPiZero

/-!
# 既存 Map^h の高次比較が誘導する π₀ 評価の正規化

概要：元の高次比較の π₀ への作用を、既存の局所化 Hom 同値へ厳密に照合する。
方針：同じ零単体の要素圏の頂点で、元の左右比較と三本矢の値を回収する。
規約：元の全 π₀ 類を扱い、任意の可換環と同じ Hom の持ち上げを保持する。
使われ方：実 DK/Map^h 高次比較と既存 π₀ 同値との一致。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra Opposite Hammock
open SerrePositivity.SimplicialModel
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : (operad A).Algebra)

def algebraReducedHammockPiZeroValue :
    let := modelCategory A
    SSet.π₀ (algebraReducedHammock A X Y) →
      ((weakEquivalences (operad A).Algebra).Q.obj X ⟶
        (weakEquivalences (operad A).Algebra).Q.obj Y) := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.toComponents (algebraReducedHammockValue A X Y)

lemma mappingSpaceReducedHammockComponentsIso_value
    (z : SSet.π₀ (SSet.uliftFunctor.{u + 1, u}.obj (((mappingSpace A).obj (op X)).obj Y))) :
    let := modelCategory A
    algebraReducedHammockPiZeroValue A X Y
        ((mappingSpaceReducedHammockComponentsIso A X Y).hom z) =
      mappingSpacePiZeroEquiv A (weakEquivalences (operad A).Algebra).Q (op X) Y
        (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.down (((mappingSpace A).obj (op X)).obj Y) z) := by
  let := modelCategory A
  obtain ⟨⟨f⟩, rfl⟩ := SSet.π₀.mk_surjective z
  let k := ComposableArrows.mk₀ (show ULiftHom.{u + 1}
    (((((mappingSpace A).obj (op X)).obj Y).Elements)ᵒᵖ) from
      op ((((mappingSpace A).obj (op X)).obj Y).elementsMk (op ⦋0⦌) f))
  have h := ConcreteCategory.congr_hom (mappingSpaceReducedHammockComponentsIso_fac A X Y)
    (SSet.π₀.mk k)
  change (mappingSpaceReducedHammockComponentsIso A X Y).hom
      (SSet.mapπ₀ (mappingSpaceIndexAugmentation A X Y) (SSet.π₀.mk k)) =
    SSet.mapπ₀ (mappingSpaceReducedHammockNerveMap A X Y) (SSet.π₀.mk k) at h
  rw [SSet.mapπ₀_mk, mappingSpaceIndexAugmentation_zero] at h
  rw [h]
  exact mappingSpaceReducedHammockNerveMap_value_zero A X Y f

lemma algebraReducedHammockPiZeroValue_bijective :
    let := modelCategory A
    Function.Bijective (algebraReducedHammockPiZeroValue A X Y) := by
  let := modelCategory A
  let e := (mappingSpaceReducedHammockComponentsIso A X Y).toEquiv
  let d := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.equiv.{u, u + 1} (((mappingSpace A).obj (op X)).obj Y)
  let h := mappingSpacePiZeroEquiv A (weakEquivalences (operad A).Algebra).Q (op X) Y
  have he : algebraReducedHammockPiZeroValue A X Y = fun z => h (d (e.symm z)) := by
    funext z
    have hz := mappingSpaceReducedHammockComponentsIso_value A X Y (e.symm z)
    change algebraReducedHammockPiZeroValue A X Y (e (e.symm z)) = h (d (e.symm z)) at hz
    rw [e.apply_symm_apply] at hz
    exact hz
  rw [he]
  exact h.bijective.comp (d.bijective.comp e.symm.bijective)

def algebraReducedHammockPiZeroEquiv :
    let := modelCategory A
    SSet.π₀ (algebraReducedHammock A X Y) ≃
      ((weakEquivalences (operad A).Algebra).Q.obj X ⟶
        (weakEquivalences (operad A).Algebra).Q.obj Y) := by
  let := modelCategory A
  exact Equiv.ofBijective (algebraReducedHammockPiZeroValue A X Y)
    (algebraReducedHammockPiZeroValue_bijective A X Y)

end SerrePositivity.EInfinity.BarrattEccles
