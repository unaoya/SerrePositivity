module
public import SerrePositivity.KST.SConstruction.CubicalPresheaf

/-! # cubical sets 上の Serre 鎖立方体の余極限延長
概要：具体的立方体上の元の鎖関手を、全 cubical sets 上の鎖複体値関手へ延長する。
方針：Yoneda に沿う点ごとの左 Kan 延長を使い、表現可能立方体上の自然同型を回収する。
規約：鎖区間の因子順は元のまま。使われ方：cubical rigidification と Serre 対角の延長。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits Opposite
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の Serre 鎖立方体を全 cubical sets に余極限で延長した関手。 -/
def cubicalSerreChains : CubicalSet.{u} ⥤ Complex A :=
  cubicalYoneda.leftKanExtension (serreConcreteCubeComplexFunctor A)

/-- 表現可能立方体での、元の Serre 鎖立方体を回収する自然な比較。 -/
def cubicalSerreChainsCubeUnit : serreConcreteCubeComplexFunctor A ⟶
    cubicalYoneda ⋙ cubicalSerreChains A :=
  cubicalYoneda.leftKanExtensionUnit (serreConcreteCubeComplexFunctor A)

/-- 余極限延長は、表現可能立方体上で元の鎖関手と自然に同型。 -/
def cubicalSerreChainsCubeIso : serreConcreteCubeComplexFunctor A ≅
    cubicalYoneda ⋙ cubicalSerreChains A := by
  letI : IsIso (cubicalSerreChainsCubeUnit A) := by
    change IsIso (uliftYoneda.{u}.leftKanExtensionUnit (serreConcreteCubeComplexFunctor A))
    infer_instance
  exact asIso (cubicalSerreChainsCubeUnit A)

/-- 元の各立方体が cubical set の鎖複体へ定める射。 -/
def cubicalSerreCell {K : CubicalSet.{u}} (c : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) (x : K.obj (op c)) :
    (serreConcreteCubeComplexFunctor A).obj c ⟶ (cubicalSerreChains A).obj K :=
  (cubicalSerreChainsCubeUnit A).app c ≫ (cubicalSerreChains A).map (cubicalCell c x)

/-- 各立方体の鎖射は cubical set の元の射について自然。 -/
lemma cubicalSerreCell_naturality {K L : CubicalSet.{u}} (f : K ⟶ L)
    (c : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) (x : K.obj (op c)) :
    cubicalSerreCell A c x ≫ (cubicalSerreChains A).map f =
      cubicalSerreCell A c (f.app (op c) x) := by
  dsimp only [cubicalSerreCell]
  rw [Category.assoc, ← Functor.map_comp, cubicalCell_naturality]

/-- 元の立方体の射に関する比較の自然性は、元の鎖射そのものを保持する。 -/
lemma cubicalSerreChainsCubeUnit_naturality {c d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube} (f : c ⟶ d) :
    (serreConcreteCubeComplexFunctor A).map f ≫ (cubicalSerreChainsCubeUnit A).app d =
      (cubicalSerreChainsCubeUnit A).app c ≫
        (cubicalSerreChains A).map (cubicalYoneda.map f) :=
  (cubicalSerreChainsCubeUnit A).naturality f

end SerrePositivity.KST.SConstruction
