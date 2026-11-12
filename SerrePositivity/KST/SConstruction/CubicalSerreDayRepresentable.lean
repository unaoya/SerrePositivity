module
public import SerrePositivity.KST.SConstruction.CubicalSerreDayNaturality

/-! # 元の表現可能立方体上の Day 鎖比較の同型性
概要：全体へ降ろした Day 鎖比較が、元の表現可能な両立方体では実際に同型であると示す。
方針：元の連結恒等 cell の鎖射が同型であることと、同じ cell の比較の回収式を使う。
規約：比較の順射は元の Day 鎖比較そのもの。使われ方：全 cubical sets への同型性の拡張。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の連結恒等 cell による鎖射を与える同型。 -/
def cubicalSerreDayCubeGeneratorIso (c d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) :
    (serreConcreteCubeComplexFunctor A).obj (concreteCubeTensorObj c d) ≅
      (cubicalSerreChains A).obj
        (cubicalDayTensor (cubicalYoneda.obj c) (cubicalYoneda.obj d)) :=
  (cubicalSerreChainsCubeIso A).app (concreteCubeTensorObj c d) ≪≫
    (cubicalSerreChains A).mapIso (cubicalDayCubeIso.{u} c d).symm

/-- 元の生成同型の鎖射は、元の連結した両恒等 cell の鎖射そのもの。 -/
lemma cubicalSerreDayCubeGeneratorIso_hom (c d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) :
    (cubicalSerreDayCubeGeneratorIso A c d).hom =
      cubicalSerreCell A (concreteCubeTensorObj c d)
        (K := cubicalDayTensor (cubicalYoneda.obj c) (cubicalYoneda.obj d))
        (cubicalDayTensorCell c d (ULift.up (𝟙 c)) (ULift.up (𝟙 d))) := rfl

/-- 元の全体比較は、元の両恒等 cell 上で同じ Serre cotensorator を回収する。 -/
lemma cubicalSerreDayCubeGenerator_comparison (c d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) :
    (cubicalSerreDayCubeGeneratorIso A c d).hom ≫
        cubicalSerreDayComparison A (cubicalYoneda.obj c) (cubicalYoneda.obj d) =
      Functor.OplaxMonoidal.δ (serreConcreteCubeComplexFunctor A) c d ≫
        ((cubicalSerreChainsCubeUnit A).app c ⊗ₘ (cubicalSerreChainsCubeUnit A).app d) := by
  erw [cubicalSerreDayCubeGeneratorIso_hom, cubicalSerreDayComparison_cell]
  dsimp only [cubicalSerreDayPair]
  erw [cubicalSerreCell_identity A c, cubicalSerreCell_identity A d]

/-- 元の両表現可能立方体上で、同じ Day 鎖比較は同型。 -/
instance cubicalSerreDayComparison_representable_isIso (c d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) :
    IsIso (cubicalSerreDayComparison A (cubicalYoneda.obj c) (cubicalYoneda.obj d)) := by
  let : IsIso ((cubicalSerreChainsCubeUnit A).app c) := by
    change IsIso ((cubicalSerreChainsCubeIso A).hom.app c)
    infer_instance
  let : IsIso ((cubicalSerreChainsCubeUnit A).app d) := by
    change IsIso ((cubicalSerreChainsCubeIso A).hom.app d)
    infer_instance
  let : IsIso ((cubicalSerreDayCubeGeneratorIso A c d).hom ≫
      cubicalSerreDayComparison A (cubicalYoneda.obj c) (cubicalYoneda.obj d)) := by
    rw [cubicalSerreDayCubeGenerator_comparison]
    infer_instance
  exact IsIso.of_isIso_comp_left (cubicalSerreDayCubeGeneratorIso A c d).hom _

/-- 元の両表現可能立方体上の、元の Day 鎖比較を順射とする同型。 -/
def cubicalSerreDayCubeComparisonIso (c d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) :
    (cubicalSerreChains A).obj
        (cubicalDayTensor (cubicalYoneda.obj c) (cubicalYoneda.obj d)) ≅
      (cubicalSerreChains A).obj (cubicalYoneda.obj c) ⊗
        (cubicalSerreChains A).obj (cubicalYoneda.obj d) :=
  asIso (cubicalSerreDayComparison A (cubicalYoneda.obj c) (cubicalYoneda.obj d))

end SerrePositivity.KST.SConstruction
