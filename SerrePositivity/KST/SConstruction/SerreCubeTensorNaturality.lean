module
public import SerrePositivity.KST.SConstruction.SerreCubeTensorRightNaturality
public import SerrePositivity.KST.SConstruction.SerreCubeTensorLeftNaturality

/-! # 元の鎖の連結 tensor 比較の二変数自然同型
概要：元の具体的立方体の両因子の射について、同じ鎖比較の自然性を証明する。
方針：元の tensor 射を左右の作用へ因数分解し、両自然性と元の tensor 合成則を使う。
規約：元の因子順と同じ比較同型を保持する。使われ方：全 cubical sets 上の鎖 tensor。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 始域・終域の次元を固定した元の両射について、連結鎖比較は自然。 -/
lemma serreCubeTensorIso_naturality_canonical {n n' m m' : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk n ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk n') (g : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk m ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk m') :
    serreConcreteCubeMap A (concreteCubeTensorMap f g) ≫ (serreCubeTensorIso A n' m').hom =
      (serreCubeTensorIso A n m).hom ≫
        serreCubeTensorHom A (n := n) (p := n') (m := m) (q := m')
          (serreConcreteCubeMap A f) (serreConcreteCubeMap A g) := by
  have hl : serreConcreteCubeMap A (concreteCubeTensorMap f (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk m))) ≫
      (serreCubeTensorIso A n' m).hom = (serreCubeTensorIso A n m).hom ≫
        serreCubeTensorHom A (n := n) (p := n') (m := m) (q := m)
          (serreConcreteCubeMap A f) (𝟙 (serreCubeComonoid A m)) :=
    serreCubeTensorIso_tensorMap_naturality_left A m f
  have hr := serreCubeRightBlockNatural_all A n' g
  dsimp only [SerreCubeRightBlockNatural] at hr
  have ht := monoidalBlocks_paste
    (R := serreCubeComonoid A (n + m)) (S := serreCubeComonoid A (n' + m))
    (T := serreCubeComonoid A (n' + m')) (X := serreCubeComonoid A n)
    (X' := serreCubeComonoid A n') (Y := serreCubeComonoid A m) (Y' := serreCubeComonoid A m')
    (serreCubeTensorIso A n m).hom (serreCubeTensorIso A n' m).hom
    (serreCubeTensorIso A n' m').hom
    (serreConcreteCubeMap A (concreteCubeTensorMap f (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk m))))
    (serreConcreteCubeMap A (concreteCubeRightBlockHom n' g))
    (serreConcreteCubeMap A f) (serreConcreteCubeMap A g) hl hr
  have hv := (congrArg
    (fun t : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (n + m) ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (n' + m') => serreConcreteCubeMap A t)
    (concreteCubeTensorMap_factor f g)).trans (serreConcreteCubeMap_comp A _ _)
  calc
    _ = (serreConcreteCubeMap A (concreteCubeTensorMap f (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk m))) ≫
        serreConcreteCubeMap A (concreteCubeRightBlockHom n' g)) ≫
          (serreCubeTensorIso A n' m').hom :=
      congrArg (fun t => t ≫ (serreCubeTensorIso A n' m').hom) hv
    _ = _ := ht

/-- 元の具体的な両射に対する、元の連結鎖比較の二変数自然性。 -/
lemma serreCubeTensorIso_naturality {X X' Y Y' : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube} (f : X ⟶ X') (g : Y ⟶ Y') :
    (serreConcreteCubeFunctor A).map (concreteCubeTensorMap f g) ≫
        (serreCubeTensorIso A X'.dimension Y'.dimension).hom =
      (serreCubeTensorIso A X.dimension Y.dimension).hom ≫
        serreCubeTensorHom A (n := X.dimension) (p := X'.dimension)
          (m := Y.dimension) (q := Y'.dimension)
          ((serreConcreteCubeFunctor A).map f) ((serreConcreteCubeFunctor A).map g) := by
  cases X
  cases X'
  cases Y
  cases Y'
  exact serreCubeTensorIso_naturality_canonical A f g

/-- 元の具体的連結積の鎖関手と tensor の二変数自然同型。 -/
def serreConcreteCubeTensorNatIso :
    concreteCubeTensor ⋙ serreConcreteCubeFunctor A ≅
      (serreConcreteCubeFunctor A).prod (serreConcreteCubeFunctor A) ⋙
        tensor (Comon (Complex A)) :=
  NatIso.ofComponents (fun P => serreCubeTensorIso A P.1.dimension P.2.dimension)
    (fun {P Q} f => by
      change (serreConcreteCubeFunctor A).map (concreteCubeTensorMap f.1 f.2) ≫
          (serreCubeTensorIso A Q.1.dimension Q.2.dimension).hom =
        (serreCubeTensorIso A P.1.dimension P.2.dimension).hom ≫
          serreCubeTensorHom A (n := P.1.dimension) (p := Q.1.dimension)
            (m := P.2.dimension) (q := Q.2.dimension)
            ((serreConcreteCubeFunctor A).map f.1) ((serreConcreteCubeFunctor A).map f.2)
      exact serreCubeTensorIso_naturality A f.1 f.2)

end SerrePositivity.KST.SConstruction
