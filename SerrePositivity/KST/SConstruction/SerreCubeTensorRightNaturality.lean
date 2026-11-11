module
public import SerrePositivity.KST.SConstruction.SerreCubeRightBlockGenerators

/-! # 元の全具体的射に関する鎖比較の右因子自然性
概要：元の右ブロックの全ての具体的射で、同じ連結比較の自然性を証明する。
方針：全生成射の可換性と元の恒等・合成保存から、生成条件で帰納する。
規約：語や射の表示に新たな仮定を置かない。使われ方：鎖の二変数自然同型。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の全生成射の鎖比較の右因子自然性。 -/
lemma serreCubeRightBlockNatural_generated (n : ℕ) {m k : ℕ}
    {f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex k} (hf : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated f) :
    SerreCubeRightBlockNatural A n (⟨f, hf⟩ : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk m ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk k) := by
  induction hf with
  | id m => exact serreCubeRightBlockNatural_id A n m
  | face b m i => exact serreCubeRightBlockNatural_face A n m b i
  | degeneracy m i => exact serreCubeRightBlockNatural_degeneracy A n m i
  | connection m i => exact serreCubeRightBlockNatural_connection A n m i
  | @comp m k l f g hf hg ihf ihg =>
    exact serreCubeRightBlockNatural_comp A n
      (⟨f, hf⟩ : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk m ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk k)
      (⟨g, hg⟩ : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk k ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk l) ihf ihg

/-- 元の右ブロックの具体的射は、表示に依存せず同じ鎖比較と可換。 -/
lemma serreCubeRightBlockNatural_all (n : ℕ) {m k : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk m ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk k) : SerreCubeRightBlockNatural A n f :=
  serreCubeRightBlockNatural_generated A n f.property

/-- 元の全具体的射について、同じ連結比較は右因子に関して自然。 -/
lemma serreCubeTensorIso_tensorMap_naturality_right (n : ℕ) {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube}
    (f : X ⟶ Y) :
    (serreConcreteCubeFunctor A).map (concreteCubeTensorMap (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk n)) f) ≫
        (serreCubeTensorIso A n Y.dimension).hom =
      (serreCubeTensorIso A n X.dimension).hom ≫
        serreCubeTensorHom A (n := n) (p := n) (m := X.dimension) (q := Y.dimension)
          (𝟙 (serreCubeComonoid A n)) ((serreConcreteCubeFunctor A).map f) := by
  cases X
  cases Y
  exact serreCubeRightBlockNatural_all A n f

end SerrePositivity.KST.SConstruction
