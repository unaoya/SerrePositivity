module
public import SerrePositivity.KST.SConstruction.CubicalSerreCellRestriction
public import SerrePositivity.KST.SConstruction.SerreConcreteCubeMonoidalRecovery
public import SerrePositivity.KST.SConstruction.CubicalDayCells

/-! # 元の二つの cubical cell の Serre 鎖の連結比較
概要：元の連結立方体から、二つの cell の鎖の tensor への射を与える。
方針：元の Serre cotensorator と元の二つの cell 鎖射の tensor を合成する。
規約：元の連結比較と因子順を保持する。使われ方：Day tensor 全体からの鎖比較の構成。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の二つの cell の Serre 鎖を、同じ連結比較によって tensor へ送る。 -/
def cubicalSerreDayPair {K L : CubicalSet.{u}} (c d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube)
    (x : K.obj (op c)) (y : L.obj (op d)) :
    (serreConcreteCubeComplexFunctor A).obj (concreteCubeTensorObj c d) ⟶
      (cubicalSerreChains A).obj K ⊗ (cubicalSerreChains A).obj L :=
  Functor.OplaxMonoidal.δ (serreConcreteCubeComplexFunctor A) c d ≫
    @tensorHom (Complex A) _ _
      ((serreConcreteCubeComplexFunctor A).obj c) ((cubicalSerreChains A).obj K)
      ((serreConcreteCubeComplexFunctor A).obj d) ((cubicalSerreChains A).obj L)
      (cubicalSerreCell A c x) (cubicalSerreCell A d y)

/-- 元の両 cell の制限は、同じ連結鎖比較の元の具体的射による前合成。 -/
lemma cubicalSerreDayPair_restrict {K L : CubicalSet.{u}} {c c' d d' : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube}
    (f : c ⟶ c') (g : d ⟶ d') (x : K.obj (op c')) (y : L.obj (op d')) :
    (serreConcreteCubeComplexFunctor A).map (concreteCubeTensorMap f g) ≫
        cubicalSerreDayPair A c' d' x y =
      cubicalSerreDayPair A c d (K.map f.op x) (L.map g.op y) := by
  dsimp only [cubicalSerreDayPair]
  erw [← Category.assoc, ← Functor.OplaxMonoidal.δ_natural
    (serreConcreteCubeComplexFunctor A) f g, Category.assoc, tensorHom_comp_tensorHom,
    cubicalSerreCell_restrict, cubicalSerreCell_restrict]

/-- 元の二つの前層の射は、元の連結 cell の鎖比較と可換。 -/
lemma cubicalSerreDayPair_naturality {K K' L L' : CubicalSet.{u}}
    (f : K ⟶ K') (g : L ⟶ L') (c d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube)
    (x : K.obj (op c)) (y : L.obj (op d)) :
    cubicalSerreDayPair A c d x y ≫
        ((cubicalSerreChains A).map f ⊗ₘ (cubicalSerreChains A).map g) =
      cubicalSerreDayPair A c d (f.app (op c) x) (g.app (op d) y) := by
  dsimp only [cubicalSerreDayPair]
  rw [Category.assoc, tensorHom_comp_tensorHom,
    cubicalSerreCell_naturality, cubicalSerreCell_naturality]

end SerrePositivity.KST.SConstruction
