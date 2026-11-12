module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellResolution
public import SerrePositivity.DifferentialGraded.Resolution.Cell
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraExtensionInfinity

/-!
概要：元の代数射に対する実 cell 代数分解の比較射と、増大の厳密な可換性。
方針：固定対象の全段比較を、一対象の自己準同型代数へ移す。
規約：関手の恒等・合成則は未主張。使われ方：分解と derivation の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open DGCategoryCellResolution
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C : Mon (Complex R)} (f : B ⟶ C)

def cellResolutionMap : cellResolution R B ⟶ cellResolution R C :=
  Mon.Hom.mk'
    (comparisonHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R C)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraPointMap R f) .star .star)
    (comparisonHom_unit R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R C)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraPointMap R f) .star)
    (comparisonHom_comp R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R C)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraPointMap R f) .star .star .star)

lemma cellResolutionMap_augmentation :
    cellResolutionMap R f ≫ cellAugmentation R C = cellAugmentation R B ≫ f := by
  apply Mon.Hom.ext
  exact comparisonHom_augmentation R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R C)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraPointMap R f) .star .star

lemma cellResolutionMap_quasiIso (hf : QuasiIso f.hom) :
    QuasiIso (cellResolutionMap R f).hom :=
  comparisonHom_quasiIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R C)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraPointMap R f) (fun _ _ ↦ hf) .star .star

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
