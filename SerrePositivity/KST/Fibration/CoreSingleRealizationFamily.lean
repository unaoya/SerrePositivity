module
public import SerrePositivity.KST.Fibration.CoreSingleFamilyCylinder
public import SerrePositivity.KST.Fibration.EnrichedObjectRelabelling

/-!
概要：元の core S 実現対象を値とする、同じ全 Hom 作用と商核円柱。
方針：単回の豊穣実現を対象等号で読み替え、評価を実現座標同型で照合する。
規約：元の全パラメータを保ち、商実現比較の可逆性は仮定しない。
使われ方：Ex∞ へ送る前の全零化族の固定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 元の core S 対角実現を、同じ閉内部 Hom を持つ対象として保持する。 -/
def coreSingleRealizationObject (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) : SSetInternalObject.{u} :=
  ⟨coreSRealizationFunctor.obj (stableCategoryModel A)⟩

/-- 元の単回実現値と core S 実現値の対象等号。 -/
theorem coreSingleRealizationObject_eq (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (stableMultiRealizationEnrichedFunctor 1).obj A = coreSingleRealizationObject A :=
  congrArg SSetInternalObject.mk (coreSingleRealization_obj_eq (stableCategoryModel A)).symm

/-- 元の core S 実現対象上へ全 Hom を読み替えた、同じ豊穣関手。 -/
def coreSingleRealizationEnrichedFunctor :
    EnrichedFunctor SSet.{u} _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u} SSetInternalObject.{u} :=
  relabelEnrichedObjects (stableMultiRealizationEnrichedFunctor 1)
    coreSingleRealizationObject (funext coreSingleRealizationObject_eq)

/-- 全 Hom の読み替えは、元の単回実現座標同型による評価の輸送と一致する。 -/
theorem coreSingleRealizationFamily_coordinates {A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} {P : SSet.{u}}
    (H : P ⟶ (A ⟶[SSet.{u}] C)) :
    uncurry (H ≫ coreSingleRealizationEnrichedFunctor.map A C) =
      ((coreSingleRealizationIso (stableCategoryModel A)).hom ▷ P) ≫
        uncurry (H ≫ (stableMultiRealizationEnrichedFunctor 1).map A C) ≫
          (coreSingleRealizationIso (stableCategoryModel C)).inv := by
  change uncurry (H ≫ (relabelEnrichedObjects (stableMultiRealizationEnrichedFunctor 1)
    coreSingleRealizationObject (funext coreSingleRealizationObject_eq)).map A C) = _
  rw [relabelEnrichedObjects_uncurry, coreSingleRealizationIso_hom_eq]
  have hi : coreSingleRealizationIso (stableCategoryModel C) =
      eqToIso (coreSingleRealization_obj_eq (stableCategoryModel C)) :=
    Iso.ext (coreSingleRealizationIso_hom_eq _)
  rw [hi]
  rfl

/-- 元の商核円柱は、元の core S 対象上の同じ豊穣実現族の評価そのもの。 -/
theorem quotientSKernelNullCylinder_coreRealization
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    quotientSKernelNullCylinder h =
      uncurry (zeroEndPostcompFamily
        (show A ⟶ C from (show A ⟶ B from i) ≫ (show B ⟶ C from q))
          (verdierSequenceComposite_zero h) ≫
            coreSingleRealizationEnrichedFunctor.map
              (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from A) (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from C)) := by
  rw [coreSingleRealizationFamily_coordinates]
  exact quotientSKernelNullCylinder_realization h

end SerrePositivity.KST.Fibration
