module
public import SerrePositivity.KST.SConstruction.CubicalSerreRepresentable
public import SerrePositivity.KST.SConstruction.CubicalSerreDayPair

/-! # 元の cell と両 cell の Serre 余モノイド射
概要：元の cell 鎖射と連結 cell の鎖比較を、余モノイド射として回収する。
方針：元の表現可能比較・前層の射・Serre cotensorator を余モノイド圏で合成する。
規約：元の underlying 鎖射を保持。使われ方：全 Day 比較の対角・増大保存。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の各 cell の鎖射を持つ余モノイド射。 -/
def cubicalSerreComonoidCell {K : CubicalSet.{u}} (c : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) (x : K.obj (op c)) :
    (serreConcreteCubeFunctor A).obj c ⟶ (cubicalSerreComonoidFunctor A).obj K :=
  (cubicalSerreComonoidCubeUnit A).app c ≫
    (cubicalSerreComonoidFunctor A).map (cubicalCell c x)

/-- 元の余モノイド cell の underlying 鎖射は同じ cell 射。 -/
lemma cubicalSerreComonoidCell_hom {K : CubicalSet.{u}} (c : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube)
    (x : K.obj (op c)) :
    (cubicalSerreComonoidCell A c x).hom = cubicalSerreCell A c x := rfl

/-- 元の二つの cell の連結鎖比較を持つ余モノイド射。 -/
def cubicalSerreComonoidDayPair {K L : CubicalSet.{u}} (c d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube)
    (x : K.obj (op c)) (y : L.obj (op d)) :
    (serreConcreteCubeFunctor A).obj (concreteCubeTensorObj c d) ⟶
      (cubicalSerreComonoidFunctor A).obj K ⊗ (cubicalSerreComonoidFunctor A).obj L :=
  Functor.OplaxMonoidal.δ (serreConcreteCubeFunctor A) c d ≫
    @tensorHom (Comon (Complex A)) _ _
      ((serreConcreteCubeFunctor A).obj c) ((cubicalSerreComonoidFunctor A).obj K)
      ((serreConcreteCubeFunctor A).obj d) ((cubicalSerreComonoidFunctor A).obj L)
      (cubicalSerreComonoidCell A c x) (cubicalSerreComonoidCell A d y)

/-- 元の鎖 cotensorator は、元の余モノイド cotensorator の underlying 射。 -/
lemma serreConcreteCubeComplex_cotensorator_hom (c d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) :
    Functor.OplaxMonoidal.δ (serreConcreteCubeComplexFunctor A) c d =
      (Functor.OplaxMonoidal.δ (serreConcreteCubeFunctor A) c d).hom := by
  change (Functor.OplaxMonoidal.δ (serreConcreteCubeFunctor A) c d).hom ≫
    𝟙 (((serreConcreteCubeFunctor A).obj c).X ⊗
      ((serreConcreteCubeFunctor A).obj d).X) = _
  exact Category.comp_id _

/-- 元の両 cell の余モノイド比較の underlying 鎖射は同じ Day 比較。 -/
lemma cubicalSerreComonoidDayPair_hom {K L : CubicalSet.{u}} (c d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube)
    (x : K.obj (op c)) (y : L.obj (op d)) :
    (cubicalSerreComonoidDayPair A c d x y).hom = cubicalSerreDayPair A c d x y := by
  dsimp only [cubicalSerreComonoidDayPair, cubicalSerreDayPair]
  rw [serreConcreteCubeComplex_cotensorator_hom]
  rfl

end SerrePositivity.KST.SConstruction
