module
public import SerrePositivity.KST.SConstruction.CubicalSerreComonoidCells
public import SerrePositivity.KST.SConstruction.CubicalSerreDayUnit

/-! # 元の Day 単位の Serre 余モノイド比較
概要：元の単位生成 cell による同型を、既存の余モノイド圏へ持ち上げる。
方針：零次元立方体の余モノイド cell と同じ鎖同型を使う。
規約：単位と逆単位の underlying 射を保持。使われ方：余モノイド値のモノイダル単位。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]
attribute [local instance] ComonObj.instTensorUnit

/-- 元の単位生成 cell は、tensor 単位の余モノイドからの射。 -/
instance cubicalSerreDayUnitGenerator_isComonHom :
    IsComonHom (cubicalSerreDayUnitIso A).inv := by
  change IsComonHom (cubicalSerreComonoidCell A (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0) cubicalDayUnitCell).hom
  exact (cubicalSerreComonoidCell A (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0) cubicalDayUnitCell).isComonHom_hom

/-- 元の Day 単位の同型を、同じ対角・増大を保つ余モノイド同型として読む。 -/
def cubicalSerreDayComonoidUnit :
    𝟙_ (Comon (Complex A)) ≅ (cubicalSerreComonoidFunctor A).obj cubicalDayUnit :=
  @Comon.mkIso' (Complex A) _ _ (𝟙_ (Comon (Complex A)))
    ((cubicalSerreComonoidFunctor A).obj cubicalDayUnit)
    (cubicalSerreDayUnitIso A).symm (cubicalSerreDayUnitGenerator_isComonHom A)

/-- 元の余モノイド単位の順射は、同じ単位生成 cell。 -/
lemma cubicalSerreDayComonoidUnit_hom :
    (cubicalSerreDayComonoidUnit A).hom.hom =
      cubicalSerreCell A (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0) cubicalDayUnitCell := rfl

/-- 元の余モノイド単位の逆射は、同じ Serre 増大。 -/
lemma cubicalSerreDayComonoidUnit_inv :
    (cubicalSerreDayComonoidUnit A).inv.hom = cubicalSerreAugmentation A cubicalDayUnit :=
  cubicalSerreDayUnitIso_augmentation A

end SerrePositivity.KST.SConstruction
