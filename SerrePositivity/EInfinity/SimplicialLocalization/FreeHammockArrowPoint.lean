module

public import SerrePositivity.EInfinity.SimplicialLocalization.FreeHammockArrowAugmentation
public import SerrePositivity.EInfinity.SimplicialLocalization.DKHammockCompositionComparison
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitArrowMap

/-!
# 元の射の点を同じ自由 hammock 比較で回収する

概要：共通始域の零単体を単位からの点にし、元の両比較で同じ点を回収する。
方針：単位からの写像と零単体の標準同値を使う。
規約：元の DK 生成射・元の hammock 射を保持する。
使われ方：高次比較の元の射への整合と前後合成の自然性。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory MonoidalCategory Opposite Hammock SerrePositivity.InfinityCategories
open SerrePositivity.SimplicialModel
open scoped Simplicial

lemma unitPointMap_comp {K L : SSet.{u}} (p : K _⦋0⦌) (f : K ⟶ L) :
    (SSet.unitHomEquiv K).symm p ≫ f = (SSet.unitHomEquiv L).symm (f.app _ p) := by
  apply (SSet.unitHomEquiv L).injective
  change f.app _ (SSet.unitHomEquiv K ((SSet.unitHomEquiv K).symm p)) =
    SSet.unitHomEquiv L ((SSet.unitHomEquiv L).symm (f.app _ p))
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {X Y : C.category}

def freeHammockArrowPoint (f : X ⟶ Y) : 𝟙_ SSet.{u} ⟶ freeHammockDiagonal C X Y :=
  (SSet.unitHomEquiv _).symm (freeHammockArrowZero C f)

def localizationArrowPoint (f : X ⟶ Y) : 𝟙_ SSet.{u} ⟶ localizationHom C X Y :=
  (SSet.unitHomEquiv _).symm (localizationArrowZero C f)

lemma freeHammockArrowPoint_comparison (f : X ⟶ Y) :
    freeHammockArrowPoint C f ≫ freeHammockDiagonalComparison C X Y =
      localizationArrowPoint C f := by
  rw [freeHammockArrowPoint, unitPointMap_comp, freeHammockArrowZero_comparison]
  rfl

lemma freeHammockArrowPoint_augmentation (f : X ⟶ Y) :
    freeHammockArrowPoint C f ≫ freeHammockDiagonalAugmentation C X Y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap C.weakEquivalences f := by
  rw [freeHammockArrowPoint, unitPointMap_comp, freeHammockArrowZero_augmentation]
  apply (SSet.unitHomEquiv _).injective
  exact (SSet.unitHomEquiv _).apply_symm_apply _

lemma dkHammockColimitComparisonIso_arrow (f : X ⟶ Y) :
    AnodyneHomotopy.anodyneQ.map (localizationArrowPoint C f) ≫
        (dkHammockColimitComparisonIso C X Y).hom =
      AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap C.weakEquivalences f) := by
  rw [← freeHammockArrowPoint_comparison, Functor.map_comp, Category.assoc,
    dkHammockColimitComparisonIso_fac, ← Functor.map_comp, freeHammockArrowPoint_augmentation]

end SerrePositivity.EInfinity.SimplicialLocalization
