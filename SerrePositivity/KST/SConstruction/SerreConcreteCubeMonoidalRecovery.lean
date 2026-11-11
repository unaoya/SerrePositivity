module
public import SerrePositivity.KST.SConstruction.SerreConcreteCubeMonoidal

/-! # 強モノイダル Serre 関手の元の比較射の回収
概要：元の関手のモノイダル構造から、同じ連結比較・単位・元の tensor 射を回収する。
方針：同じ構造射の定義と二変数自然性を使い、鎖複体値の忘却関手へ接続する。
規約：比較を別の同型に置換しない。使われ方：cubical Serre 鎖の tensor 延長。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の Serre tensorator は、元の連結比較の逆射そのもの。 -/
lemma serreConcreteCube_tensorator (X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) :
    Functor.LaxMonoidal.μ (serreConcreteCubeFunctor A) X Y =
      (serreCubeTensorIso A X.dimension Y.dimension).inv := rfl

/-- 元の Serre cotensorator は、元の連結比較の順射そのもの。 -/
lemma serreConcreteCube_cotensorator (X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) :
    Functor.OplaxMonoidal.δ (serreConcreteCubeFunctor A) X Y =
      (serreCubeTensorIso A X.dimension Y.dimension).hom := rfl

/-- 元の零次元立方体の単位射は、元の単位余モノイドの恒等射。 -/
lemma serreConcreteCube_unit :
    Functor.LaxMonoidal.ε (serreConcreteCubeFunctor A) = 𝟙 (𝟙_ (Comon (Complex A))) := rfl

/-- 元の零次元立方体の逆単位射も、元の単位余モノイドの恒等射。 -/
lemma serreConcreteCube_counit :
    Functor.OplaxMonoidal.η (serreConcreteCubeFunctor A) = 𝟙 (𝟙_ (Comon (Complex A))) := rfl

/-- 元の連結射の評価は、同じ tensor 射を元の連結比較で移送したもの。 -/
lemma serreConcreteCube_map_tensor {X X' Y Y' : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube} (f : X ⟶ X') (g : Y ⟶ Y') :
    (serreConcreteCubeFunctor A).map (concreteCubeTensorMap f g) =
      (serreCubeTensorIso A X.dimension Y.dimension).hom ≫
        serreCubeTensorHom A (n := X.dimension) (p := X'.dimension)
          (m := Y.dimension) (q := Y'.dimension)
          ((serreConcreteCubeFunctor A).map f) ((serreConcreteCubeFunctor A).map g) ≫
            (serreCubeTensorIso A X'.dimension Y'.dimension).inv := by
  apply (cancel_mono (serreCubeTensorIso A X'.dimension Y'.dimension).hom).mp
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact serreCubeTensorIso_naturality A f g

/-- 元の鎖複体値 Serre 関手も、同じ連結積を保つ強モノイダル関手。 -/
instance serreConcreteCubeComplexMonoidal : (serreConcreteCubeComplexFunctor A).Monoidal := by
  change (serreConcreteCubeFunctor A ⋙ Comon.forget (Complex A)).Monoidal
  infer_instance

end SerrePositivity.KST.SConstruction
