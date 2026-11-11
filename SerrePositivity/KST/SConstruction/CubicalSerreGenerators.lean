module
public import SerrePositivity.KST.SConstruction.CubicalSerreColimit

/-! # 鎖立方体の生成射と表示関係
概要：表現可能立方体からの元の射を鎖射へ移し、全表示関係と自然性を回収する。
方針：左 Kan 延長の単位の自然性と、元の Serre 余モノイド射の保存則を使う。
規約：すべての具体的立方体の射を扱う。使われ方：Serre 対角の余極限による降下。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits Opposite MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の表現可能立方体からの射が定める鎖射。 -/
def cubicalSerreGenerator {K : CubicalSet.{u}} {c : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube}
    (φ : cubicalYoneda.obj c ⟶ K) :
    (serreConcreteCubeComplexFunctor A).obj c ⟶ (cubicalSerreChains A).obj K :=
  (cubicalSerreChainsCubeUnit A).app c ≫ (cubicalSerreChains A).map φ

/-- 恒等な立方体表示は、元の比較単位射を回収する。 -/
lemma cubicalSerreGenerator_id (c : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) :
    cubicalSerreGenerator A (𝟙 (cubicalYoneda.obj c)) =
      (cubicalSerreChainsCubeUnit A).app c := by
  dsimp only [cubicalSerreGenerator]
  exact (congrArg (fun f => (cubicalSerreChainsCubeUnit A).app c ≫ f)
    ((cubicalSerreChains A).map_id (cubicalYoneda.obj c))).trans (Category.comp_id _)

/-- 元の各 cell の鎖射は、その Yoneda 射の鎖射そのもの。 -/
lemma cubicalSerreGenerator_cell {K : CubicalSet.{u}} (c : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube)
    (x : K.obj (op c)) :
    cubicalSerreGenerator A (cubicalCell c x) = cubicalSerreCell A c x := rfl

/-- 元の立方体の全表示関係を、同じ鎖射の等号として回収する。 -/
lemma cubicalSerreGenerator_relation {K : CubicalSet.{u}} {c d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube}
    (f : c ⟶ d) (φ : cubicalYoneda.obj d ⟶ K) :
    (serreConcreteCubeComplexFunctor A).map f ≫ cubicalSerreGenerator A φ =
      cubicalSerreGenerator A (cubicalYoneda.map f ≫ φ) := by
  dsimp only [cubicalSerreGenerator]
  rw [← Category.assoc, cubicalSerreChainsCubeUnit_naturality]
  rw [Category.assoc, ← Functor.map_comp]

/-- cubical set の元の射は、各生成鎖射との後合成を回収する。 -/
lemma cubicalSerreGenerator_naturality {K L : CubicalSet.{u}} (f : K ⟶ L)
    {c : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube} (φ : cubicalYoneda.obj c ⟶ K) :
    cubicalSerreGenerator A φ ≫ (cubicalSerreChains A).map f =
      cubicalSerreGenerator A (φ ≫ f) := by
  dsimp only [cubicalSerreGenerator]
  rw [Category.assoc, ← Functor.map_comp]

/-- 元の鎖関手の対象型を保った Serre 対角。 -/
def serreConcreteCubeDiagonal (c : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) :
    (serreConcreteCubeComplexFunctor A).obj c ⟶
      (serreConcreteCubeComplexFunctor A).obj c ⊗ (serreConcreteCubeComplexFunctor A).obj c :=
  serreCubeDiagonal A c.dimension

/-- 元の鎖関手の対象型を保った Serre 増大。 -/
def serreConcreteCubeAugmentation (c : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) :
    (serreConcreteCubeComplexFunctor A).obj c ⟶ 𝟙_ (Complex A) :=
  serreCubeAugmentation A c.dimension

/-- 具体的な全立方体の元の鎖射は Serre 対角を保つ。 -/
lemma serreConcreteCubeComplexFunctor_comul {c d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube} (f : c ⟶ d) :
    (serreConcreteCubeComplexFunctor A).map f ≫ serreConcreteCubeDiagonal A d =
      serreConcreteCubeDiagonal A c ≫
        ((serreConcreteCubeComplexFunctor A).map f ⊗ₘ
          (serreConcreteCubeComplexFunctor A).map f) :=
  IsComonHom.hom_comul ((serreConcreteCubeFunctor A).map f).hom

/-- 具体的な全立方体の元の鎖射は Serre 増大を保つ。 -/
lemma serreConcreteCubeComplexFunctor_counit {c d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube} (f : c ⟶ d) :
    (serreConcreteCubeComplexFunctor A).map f ≫ serreConcreteCubeAugmentation A d =
      serreConcreteCubeAugmentation A c :=
  IsComonHom.hom_counit ((serreConcreteCubeFunctor A).map f).hom

end SerrePositivity.KST.SConstruction
