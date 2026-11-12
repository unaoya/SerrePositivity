module
public import SerrePositivity.KST.SConstruction.CubicalSerreDayIso
public import SerrePositivity.KST.SConstruction.CubicalSerreTripleColimit
public import SerrePositivity.KST.SConstruction.CubicalDayStructuralCells

/-! # 三つの元の cell 上での Day 鎖組み立ての回収
概要：両順序の反復組み立てを、元の Serre tensorator と連結 cell で回収する。
方針：tensor 射の合成保存と元の逆比較の全 cell の回収式を二回使う。
規約：左結合した始域と元の因子順を固定。使われ方：Day 鎖の結合整合性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の左結合した二回の組み立ての、三 cell 上の評価。 -/
lemma cubicalSerreDayInverse_leftTriple {K L M : CubicalSet.{u}}
    (a b c : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) (x : K.obj (op a)) (y : L.obj (op b)) (z : M.obj (op c)) :
    cubicalSerreCellTriple A a b c x y z ≫
        cubicalSerreDayInverse A K L ▷ (cubicalSerreChains A).obj M ≫
          cubicalSerreDayInverse A (cubicalDayTensor K L) M =
      Functor.LaxMonoidal.μ (serreConcreteCubeComplexFunctor A) a b ▷
          (serreConcreteCubeComplexFunctor A).obj c ≫
        Functor.LaxMonoidal.μ (serreConcreteCubeComplexFunctor A)
          (concreteCubeTensorObj a b) c ≫
        cubicalSerreCell A (concreteCubeTensorObj (concreteCubeTensorObj a b) c)
          (cubicalDayTensorCell (concreteCubeTensorObj a b) c
            (cubicalDayTensorCell a b x y) z) := by
  dsimp only [cubicalSerreCellTriple, cubicalSerreCellTensor]
  rw [← tensorHom_id, ← Category.assoc, tensorHom_comp_tensorHom,
    cubicalSerreDayInverse_cell, Category.comp_id]
  dsimp only [cubicalSerreDayAssembly]
  rw [← Category.id_comp (cubicalSerreCell A c z), ← tensorHom_comp_tensorHom,
    tensorHom_id, Category.assoc, cubicalSerreDayInverse_cell]
  rfl

/-- 元の右結合した二回の組み立ての、三 cell 上の評価。 -/
lemma cubicalSerreDayInverse_rightTriple {K L M : CubicalSet.{u}}
    (a b c : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) (x : K.obj (op a)) (y : L.obj (op b)) (z : M.obj (op c)) :
    cubicalSerreCellTriple A a b c x y z ≫
        (α_ ((cubicalSerreChains A).obj K) ((cubicalSerreChains A).obj L)
          ((cubicalSerreChains A).obj M)).hom ≫
        (cubicalSerreChains A).obj K ◁ cubicalSerreDayInverse A L M ≫
          cubicalSerreDayInverse A K (cubicalDayTensor L M) =
      (α_ ((serreConcreteCubeComplexFunctor A).obj a)
        ((serreConcreteCubeComplexFunctor A).obj b)
        ((serreConcreteCubeComplexFunctor A).obj c)).hom ≫
        (serreConcreteCubeComplexFunctor A).obj a ◁
          Functor.LaxMonoidal.μ (serreConcreteCubeComplexFunctor A) b c ≫
        Functor.LaxMonoidal.μ (serreConcreteCubeComplexFunctor A)
          a (concreteCubeTensorObj b c) ≫
        cubicalSerreCell A (concreteCubeTensorObj a (concreteCubeTensorObj b c))
          (cubicalDayTensorCell a (concreteCubeTensorObj b c) x
            (cubicalDayTensorCell b c y z)) := by
  dsimp only [cubicalSerreCellTriple, cubicalSerreCellTensor]
  rw [associator_naturality_assoc, ← id_tensorHom,
    ← Category.assoc (cubicalSerreCell A a x ⊗ₘ
      (cubicalSerreCell A b y ⊗ₘ cubicalSerreCell A c z)),
    tensorHom_comp_tensorHom, Category.comp_id, cubicalSerreDayInverse_cell]
  dsimp only [cubicalSerreDayAssembly]
  rw [← Category.id_comp (cubicalSerreCell A a x), ← tensorHom_comp_tensorHom,
    id_tensorHom, Category.assoc, cubicalSerreDayInverse_cell]
  rfl

end SerrePositivity.KST.SConstruction
