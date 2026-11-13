module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellResolution
public import SerrePositivity.KST.LocalizingInvariants.DGCellAugmentationFilling
public import SerrePositivity.KST.LocalizingInvariants.CochainKernelHomology

/-!
概要：実 dg 代数 cell augmentation の全境界充填・次数ごとの全射性・非輪 kernel。
方針：元の固定対象の充填を一対象に適用し、kernel 短完全列へ接続する。
規約：源代数の cofibrant 性はまだ主張しない。使われ方：derivation の持ち上げ条件。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B : Mon (Complex R))

lemma cellAugmentation_fills (c : ComplexBoundaryCell R (cellAugmentation R B).hom) :
    c.HasFilling R :=
  dgCellAugmentation_fills R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R B) .star .star c

lemma cellAugmentation_surjective (n : ℤ) :
    Function.Surjective ((cellAugmentation R B).hom.f n) :=
  cochain_surjective_of_boundaryFilling _ (cellAugmentation_fills R B) n

instance cellAugmentation_component_epi (n : ℤ) : Epi ((cellAugmentation R B).hom.f n) :=
  cochain_component_epi_of_boundaryFilling _ (cellAugmentation_fills R B) n

instance cellAugmentation_epi : Epi (cellAugmentation R B).hom :=
  HomologicalComplex.epi_of_epi_f _ (fun _ ↦ inferInstance)

lemma cellAugmentation_kernel_acyclic : (kernel (cellAugmentation R B).hom).Acyclic :=
  (cochainKernelSequence_shortExact (cellAugmentation R B).hom).acyclic_X₁
    (cellAugmentation_quasiIso R B)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
