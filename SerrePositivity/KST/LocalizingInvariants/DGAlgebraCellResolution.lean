module

public import SerrePositivity.KST.LocalizingInvariants.DGEndAlgebra
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomology
public import SerrePositivity.DifferentialGraded.Resolution.Cell
public import SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraDerivedInfinity

/-!
概要：一対象 dg 圏の固定対象 cell 分解から、実 dg 代数の分解と augmentation を構成する。
方針：元の唯一の対象の自己準同型と元の増大 dg 関手を使う。
規約：K-flat 性を持ち上げ性の代用にしない。使われ方：Postnikov derivation の始域。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B : Mon (Complex R))

abbrev CellSource := DGCategoryCellResolution.Source R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R B)

def cellSourcePoint : CellSource R B := ⟨_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint.star⟩

def cellResolution : Mon (Complex R) := dgEndAlgebra R (CellSource R B) (cellSourcePoint R B)

def cellAugmentation : cellResolution R B ⟶ B := by
  let F := DGCategoryCellResolution.augmentation R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R B)
  exact Mon.Hom.mk' (F.map (cellSourcePoint R B) (cellSourcePoint R B))
    (F.map_id (cellSourcePoint R B))
    (F.map_comp (cellSourcePoint R B) (cellSourcePoint R B) (cellSourcePoint R B))

lemma cellAugmentation_quasiIso : QuasiIso (cellAugmentation R B).hom :=
  DGCategoryCellResolution.augmentation_homQuasiIso R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R B)
    (cellSourcePoint R B) (cellSourcePoint R B)

lemma cellResolution_kFlat : complexKFlat R (cellResolution R B).X :=
  DGCategoryCellResolution.source_homKFlat R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R B)
    (cellSourcePoint R B) (cellSourcePoint R B)

lemma cellResolution_isConnective (hB : IsConnective R B) :
    IsConnective R (cellResolution R B) := by
  have : QuasiIso (cellAugmentation R B).hom := cellAugmentation_quasiIso R B
  have : B.X.IsLE 0 := hB
  apply (CochainComplex.isLE_iff _ 0).2
  intro i hi
  exact (exactAt_iff_of_quasiIsoAt (cellAugmentation R B).hom i).2
    (CochainComplex.exactAt_of_isLE B.X 0 i hi)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
