module
public import SerrePositivity.KST.SConstruction.SerreCubeTensorAssociativity
public import SerrePositivity.KST.SConstruction.SerreConcreteCubeStructuralMaps
public import SerrePositivity.KST.SConstruction.SerreCubeTensorNaturality
public import SerrePositivity.KST.SConstruction.ConcreteCubeMonoidal

/-! # 元の連結比較による Serre 立方体関手の強モノイダル構造
概要：元の二変数自然同型と結合・左右単位の整合性を、元の関手へ束ねる。
方針：tensorator は元の連結比較の逆同型、単位は元の零次元立方体の恒等同型とする。
規約：元の関手と元の全比較射を保つ。使われ方：cubical Serre 鎖と dg 豊穣合成。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の具体的結合同型の像と、元の連結鎖比較の可換性。 -/
lemma serreConcreteCube_tensor_associativity (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) :
    (serreCubeTensorIso A (X.dimension + Y.dimension) Z.dimension).hom ≫
        serreCubeLeftSplit A X.dimension Y.dimension Z.dimension ≫
          serreCubeAssociatorHom A X.dimension Y.dimension Z.dimension =
      (serreConcreteCubeFunctor A).map (concreteCubeAssociator X Y Z).hom ≫
        (serreCubeTensorIso A X.dimension (Y.dimension + Z.dimension)).hom ≫
          serreCubeRightSplit A X.dimension Y.dimension Z.dimension := by
  erw [serreConcreteCubeFunctor_associator A X Y Z]
  have h := serreCubeTensorAssociative_all A X.dimension Y.dimension Z.dimension
  dsimp only [SerreCubeTensorAssociative, MonoidalPowerCoherenceEquation] at h
  exact h.symm

/-- 元の Serre 関手の、同じ連結・単位比較を持つモノイダル構造のデータ。 -/
def serreConcreteCubeCoreMonoidal : (serreConcreteCubeFunctor A).CoreMonoidal :=
  Functor.CoreMonoidal.mk' (F := serreConcreteCubeFunctor A) (Iso.refl _)
    (fun X Y => (serreCubeTensorIso A X.dimension Y.dimension).symm)
    (μIso_inv_natural_left := by
      intro X Y f X'
      change (serreCubeTensorIso A X.dimension X'.dimension).hom ≫
          serreCubeTensorHom A (n := X.dimension) (p := Y.dimension)
            (m := X'.dimension) (q := X'.dimension)
            ((serreConcreteCubeFunctor A).map f) (𝟙 (serreCubeComonoid A X'.dimension)) =
        (serreConcreteCubeFunctor A).map (concreteCubeTensorMap f (𝟙 X')) ≫
          (serreCubeTensorIso A Y.dimension X'.dimension).hom
      exact (serreCubeTensorIso_tensorMap_naturality_left A X'.dimension f).symm)
    (μIso_inv_natural_right := by
      intro X Y X' f
      change (serreCubeTensorIso A X'.dimension X.dimension).hom ≫
          serreCubeTensorHom A (n := X'.dimension) (p := X'.dimension)
            (m := X.dimension) (q := Y.dimension)
            (𝟙 (serreCubeComonoid A X'.dimension)) ((serreConcreteCubeFunctor A).map f) =
        (serreConcreteCubeFunctor A).map (concreteCubeTensorMap (𝟙 X') f) ≫
          (serreCubeTensorIso A X'.dimension Y.dimension).hom
      exact (serreCubeTensorIso_tensorMap_naturality_right A X'.dimension f).symm)
    (oplax_associativity := by
      intro X Y Z
      change (serreCubeTensorIso A (X.dimension + Y.dimension) Z.dimension).hom ≫
          serreCubeLeftSplit A X.dimension Y.dimension Z.dimension ≫
            serreCubeAssociatorHom A X.dimension Y.dimension Z.dimension =
        (serreConcreteCubeFunctor A).map (concreteCubeAssociator X Y Z).hom ≫
          (serreCubeTensorIso A X.dimension (Y.dimension + Z.dimension)).hom ≫
            serreCubeRightSplit A X.dimension Y.dimension Z.dimension
      exact serreConcreteCube_tensor_associativity A X Y Z)
    (oplax_left_unitality := by
      intro X
      change (λ_ (serreCubeComonoid A X.dimension)).inv =
        (serreConcreteCubeFunctor A).map (concreteCubeLeftUnitor X).inv ≫
          (serreCubeTensorIso A 0 X.dimension).hom ≫
            (𝟙 (𝟙_ (Comon (Complex A))) ▷ serreCubeComonoid A X.dimension)
      erw [id_whiskerRight, Category.comp_id]
      exact serreConcreteCube_leftUnit_inv A X)
    (oplax_right_unitality := by
      intro X
      change (ρ_ (serreCubeComonoid A X.dimension)).inv =
        (serreConcreteCubeFunctor A).map (concreteCubeRightUnitor X).inv ≫
          (serreCubeTensorIso A X.dimension 0).hom ≫
            (serreCubeComonoid A X.dimension ◁ 𝟙 (𝟙_ (Comon (Complex A))))
      erw [whiskerLeft_id, Category.comp_id]
      exact serreConcreteCube_rightUnit_inv A X)

/-- 元の具体的連結積と全構造射を保つ、Serre 立方体関手の強モノイダル構造。 -/
instance serreConcreteCubeMonoidal : (serreConcreteCubeFunctor A).Monoidal :=
  (serreConcreteCubeCoreMonoidal A).toMonoidal

end SerrePositivity.KST.SConstruction
