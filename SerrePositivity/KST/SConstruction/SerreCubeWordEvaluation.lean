module
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.CubeWordRealization
public import SerrePositivity.KST.SConstruction.SerreCubeCoordinateMaps

/-! # 元の Serre 鎖写像による生成語の評価
概要：自由な cubical 生成語を、既存の全座標の Serre 余モノイド射へ評価する。
方針：面・退化・max の元の射を prefunctor に束ね、path 圏の関手へ延長する。
規約：具体的な関数の等号による降下は別途必要。使われ方：表示非依存性の検証対象。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の cubical 生成射を元の Serre 余モノイド射へ送る。 -/
def serreCubeGeneratorPrefunctor : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject ⥤q Comon (Complex A) where
  obj X := serreCubeComonoid A X.dimension
  map {X Y} f := by
    cases X
    cases Y
    cases f with
    | face b n i => exact serreCubeFace A b _ i
    | degeneracy n i => exact serreCubeDegeneracy A _ i
    | connection n i => exact serreCubeConnection A _ i

/-- 元の Serre 余モノイド射を合成した、自由な生成語の評価関手。 -/
def serreCubeWordFunctor : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWords ⥤ Comon (Complex A) :=
  Paths.lift (serreCubeGeneratorPrefunctor A)

/-- 元の Serre 鎖写像を合成した、自由な生成語の評価関手。 -/
def serreCubeWordComplexFunctor : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWords ⥤ Complex A :=
  serreCubeWordFunctor A ⋙ Comon.forget (Complex A)

/-- 一文字の語の Serre 評価は元の座標射。 -/
lemma serreCubeWordFunctor_generator {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject} (f : X ⟶ Y) :
    (serreCubeWordFunctor A).map f.toPath = (serreCubeGeneratorPrefunctor A).map f :=
  Paths.lift_toPath _ f

/-- 面の一文字の語は、元の同じ座標の Serre 面を回収する。 -/
lemma serreCubeWordFunctor_face (b : Bool) (n : ℕ) (i : Fin (n + 1)) :
    (serreCubeWordFunctor A).map
      (show _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk n ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk (n + 1) from
        _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeGenerator.face b n i).toPath = serreCubeFace A b n i := by
  exact serreCubeWordFunctor_generator A _

/-- 退化の一文字の語は、元の同じ座標の Serre 退化を回収する。 -/
lemma serreCubeWordFunctor_degeneracy (n : ℕ) (i : Fin (n + 1)) :
    (serreCubeWordFunctor A).map
      (show _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk (n + 1) ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk n from
        _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeGenerator.degeneracy n i).toPath = serreCubeDegeneracy A n i := by
  exact serreCubeWordFunctor_generator A _

/-- connection の一文字の語は、元の同じ座標の Serre max を回収する。 -/
lemma serreCubeWordFunctor_connection (n : ℕ) (i : Fin (n + 1)) :
    (serreCubeWordFunctor A).map
      (show _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk (n + 2) ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk (n + 1) from
        _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeGenerator.connection n i).toPath = serreCubeConnection A n i := by
  exact serreCubeWordFunctor_generator A _

/-- 語の評価を鎖写像へ忘却しても、同じ元の Serre 射を保つ。 -/
lemma serreCubeWordComplexFunctor_map {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWords} (f : X ⟶ Y) :
    (serreCubeWordComplexFunctor A).map f = ((serreCubeWordFunctor A).map f).hom := rfl

/-- 語の Serre 評価は、余モノイド圏で元の合成を保存する。 -/
lemma serreCubeWordFunctor_comp {X Y Z : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWords} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (serreCubeWordFunctor A).map (f ≫ g) =
      (serreCubeWordFunctor A).map f ≫ (serreCubeWordFunctor A).map g :=
  (serreCubeWordFunctor A).map_comp f g

end SerrePositivity.KST.SConstruction
