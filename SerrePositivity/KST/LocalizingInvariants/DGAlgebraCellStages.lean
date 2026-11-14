module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellResolution

/-!
概要：固定対象 cell 分解の各有限段を、実 dg 代数と遷移・包含・増大射として供給する。
方針：各段の唯一の対象の自己準同型を使い、元の三つの厳密な可換式を保持する。
規約：源の既存 dg 圏 instance は変更しない。使われ方：cell 持ち上げの段階帰納法。
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
variable (R : Type u) [CommRing R] (B : Mon (Complex R))

def cellStagePoint (n : ℕ) : (stage R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R B) n).Objects := ⟨.star⟩

def cellStage (n : ℕ) : Mon (Complex R) :=
  dgEndAlgebra R (stage R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R B) n).Objects (cellStagePoint R B n)

def cellStageAugmentation (n : ℕ) : cellStage R B n ⟶ B :=
  Mon.Hom.mk' (stageAugmentation R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R B) n .star .star)
    ((stage R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R B) n).map_id .star)
    ((stage R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R B) n).map_comp .star .star .star)

def cellStageTransition (n : ℕ) : cellStage R B n ⟶ cellStage R B (n + 1) :=
  Mon.Hom.mk' (transition R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R B) n .star .star)
    ((stage R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R B) n).transition_id .star)
    ((stage R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R B) n).transition_comp .star .star .star)

def cellStageInclusion (n : ℕ) : cellStage R B n ⟶ cellResolution R B :=
  Mon.Hom.mk' (stageInclusion R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R B) n .star .star)
    (candidateUnit_stage R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R B) n .star)
    (candidateComposition_stage R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R B) n .star .star .star).symm

lemma cellStageTransition_augmentation (n : ℕ) :
    cellStageTransition R B n ≫ cellStageAugmentation R B (n + 1) =
      cellStageAugmentation R B n := by
  apply Mon.Hom.ext
  exact transition_augmentation R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R B) n .star .star

lemma cellStageInclusion_augmentation (n : ℕ) :
    cellStageInclusion R B n ≫ cellAugmentation R B = cellStageAugmentation R B n := by
  apply Mon.Hom.ext
  exact stageInclusion_augmentation R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R B) n .star .star

lemma cellStageTransition_inclusion (n : ℕ) :
    cellStageTransition R B n ≫ cellStageInclusion R B (n + 1) = cellStageInclusion R B n := by
  apply Mon.Hom.ext
  exact transition_inclusion R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R B) n .star .star

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
