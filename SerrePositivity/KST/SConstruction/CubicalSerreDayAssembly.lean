module
public import SerrePositivity.KST.SConstruction.CubicalSerreDayComparison

/-! # 元の両 cell の tensor から Day 鎖への組み立て
概要：元の Serre tensorator を使い、両立方体の鎖を連結 cell の鎖へ送る。
方針：元の tensorator の自然性と Day cell の制限関係を合成する。
規約：因子順と元の連結比較を保持。使われ方：全体の Day 鎖比較の逆射。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の二つの cell の鎖の tensor を元の連結 cell の鎖へ組み立てる。 -/
def cubicalSerreDayAssembly {K L : CubicalSet.{u}} (c d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube)
    (x : K.obj (op c)) (y : L.obj (op d)) :
    (serreConcreteCubeComplexFunctor A).obj c ⊗
        (serreConcreteCubeComplexFunctor A).obj d ⟶
      (cubicalSerreChains A).obj (cubicalDayTensor K L) :=
  Functor.LaxMonoidal.μ (serreConcreteCubeComplexFunctor A) c d ≫
    cubicalSerreCell A (concreteCubeTensorObj c d) (cubicalDayTensorCell c d x y)

/-- 元の両 cell の制限は同じ組み立てと可換。 -/
lemma cubicalSerreDayAssembly_restrict {K L : CubicalSet.{u}} {c c' d d' : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube}
    (f : c ⟶ c') (g : d ⟶ d') (x : K.obj (op c')) (y : L.obj (op d')) :
    ((serreConcreteCubeComplexFunctor A).map f ⊗ₘ
        (serreConcreteCubeComplexFunctor A).map g) ≫
        cubicalSerreDayAssembly A c' d' x y =
      cubicalSerreDayAssembly A c d (K.map f.op x) (L.map g.op y) := by
  dsimp only [cubicalSerreDayAssembly]
  erw [← Category.assoc, Functor.LaxMonoidal.μ_natural, Category.assoc,
    cubicalSerreCell_restrict, cubicalDayTensorCell_restrict]
  rfl

/-- 元の組み立ての後の比較は、元の両 cell の鎖射の tensor。 -/
lemma cubicalSerreDayAssembly_comparison {K L : CubicalSet.{u}}
    (c d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) (x : K.obj (op c)) (y : L.obj (op d)) :
    cubicalSerreDayAssembly A c d x y ≫ cubicalSerreDayComparison A K L =
      cubicalSerreCell A c x ⊗ₘ cubicalSerreCell A d y := by
  dsimp only [cubicalSerreDayAssembly]
  rw [Category.assoc, cubicalSerreDayComparison_cell]
  dsimp only [cubicalSerreDayPair]
  rw [← Category.assoc, Functor.Monoidal.μ_δ, Category.id_comp]

/-- 元の cotensorator の後の組み立ては、同じ連結 cell の鎖射。 -/
lemma cubicalSerreDayAssembly_cotensorator {K L : CubicalSet.{u}}
    (c d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) (x : K.obj (op c)) (y : L.obj (op d)) :
    Functor.OplaxMonoidal.δ (serreConcreteCubeComplexFunctor A) c d ≫
        cubicalSerreDayAssembly A c d x y =
      cubicalSerreCell A (concreteCubeTensorObj c d) (cubicalDayTensorCell c d x y) := by
  dsimp only [cubicalSerreDayAssembly]
  rw [← Category.assoc, Functor.Monoidal.δ_μ, Category.id_comp]

end SerrePositivity.KST.SConstruction
