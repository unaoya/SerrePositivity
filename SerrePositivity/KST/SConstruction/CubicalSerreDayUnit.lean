module
public import SerrePositivity.KST.SConstruction.CubicalSerreDayRepresentable
public import SerrePositivity.KST.SConstruction.CubicalSerreDiagonal
public import SerrePositivity.KST.SConstruction.CubicalDayUnit

/-! # 元の Day 単位と Serre 鎖の単位比較
概要：元の Day 単位の鎖複体と鎖の tensor 単位との同型を与える。
方針：元の零次元表現可能単位と同じ Kan 単位の同型を合成する。
規約：順射は元の Serre 増大と照合する。使われ方：Day Serre 鎖のモノイダル単位。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の Day 単位の鎖と tensor 単位との同型。 -/
def cubicalSerreDayUnitIso : (cubicalSerreChains A).obj cubicalDayUnit.{u} ≅ 𝟙_ (Complex A) :=
  (cubicalSerreChains A).mapIso cubicalDayUnitIso.{u} ≪≫
    ((cubicalSerreChainsCubeIso A).app (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0)).symm

/-- 元の単位生成 cell による鎖射の同型。 -/
def cubicalSerreDayUnitGeneratorIso :
    𝟙_ (Complex A) ≅ (cubicalSerreChains A).obj cubicalDayUnit.{u} :=
  (cubicalSerreChainsCubeIso A).app (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0) ≪≫
    (cubicalSerreChains A).mapIso cubicalDayUnitIso.{u}.symm

/-- 元の単位生成同型の順射は、元の単位生成 cell の鎖射。 -/
lemma cubicalSerreDayUnitGeneratorIso_hom :
    (cubicalSerreDayUnitGeneratorIso A).hom =
      cubicalSerreCell A (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0) cubicalDayUnitCell.{u} := rfl

/-- 元の単位比較と単位生成 cell の比較は、同じ逆射を持つ。 -/
lemma cubicalSerreDayUnitIso_hom :
    (cubicalSerreDayUnitIso A).hom = (cubicalSerreDayUnitGeneratorIso A).inv := rfl

/-- 元の単位比較は、元の単位生成 cell を tensor 単位の恒等射へ送る。 -/
lemma cubicalSerreDayUnitIso_cell :
    cubicalSerreCell A (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0) cubicalDayUnitCell.{u} ≫
        (cubicalSerreDayUnitIso A).hom = 𝟙 (𝟙_ (Complex A)) := by
  rw [← cubicalSerreDayUnitGeneratorIso_hom, cubicalSerreDayUnitIso_hom]
  exact (cubicalSerreDayUnitGeneratorIso A).hom_inv_id

/-- 元の Day 単位の比較の順射は、既存の元の Serre 増大そのもの。 -/
lemma cubicalSerreDayUnitIso_augmentation :
    (cubicalSerreDayUnitIso A).hom = cubicalSerreAugmentation A cubicalDayUnit.{u} := by
  apply (cancel_epi (cubicalSerreDayUnitGeneratorIso A).hom).mp
  have h := cubicalSerreAugmentation_generator A cubicalDayUnit.{u}
    (cubicalCell (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0) cubicalDayUnitCell.{u})
  change cubicalSerreCell A (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0) cubicalDayUnitCell.{u} ≫
      cubicalSerreAugmentation A cubicalDayUnit.{u} = 𝟙 (𝟙_ (Complex A)) at h
  rw [cubicalSerreDayUnitGeneratorIso_hom]
  exact (cubicalSerreDayUnitIso_cell A).trans h.symm

end SerrePositivity.KST.SConstruction
