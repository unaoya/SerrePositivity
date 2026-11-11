module
public import SerrePositivity.KST.SConstruction.SerreCubeWordIndependence

/-! # 具体的立方体圏上の厳密な Serre 鎖立方体関手
概要：元の Bool 立方体の生成関数を射とする圏から Serre 余モノイド圏への関手を構成する。
方針：各射の語を一つ選び、全語の表示非依存性から恒等・合成を厳密に回収する。
規約：右端からの座標と元の鎖写像を保持する。使われ方：dg 入力の cubical rigidification。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded

/-- 元の具体的な立方体の射を実現する一つの生成語。 -/
def concreteCubeWord {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube} (f : X ⟶ Y) :
    Quiver.Path (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk X.dimension) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk Y.dimension) :=
  Classical.choose (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeMapGenerated_exists_word f.property)

/-- 選んだ語は元の具体的な頂点写像そのものを回収する。 -/
lemma concreteCubeWord_vertex {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube} (f : X ⟶ Y) :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor.map (concreteCubeWord f)).val = f.val :=
  Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeMapGenerated_exists_word f.property)

variable (A : Type u) [CommRing A]

/-- 具体的な立方体圏上の、元の Serre 余モノイド射を持つ厳密な関手。 -/
def serreConcreteCubeFunctor : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube ⥤ Comon (Complex A) where
  obj X := serreCubeComonoid A X.dimension
  map f := (serreCubeWordFunctor A).map (concreteCubeWord f)
  map_id X := by
    have h := serreCubeWordFunctor_eq_of_vertex_eq A (concreteCubeWord (𝟙 X))
      (Quiver.Path.nil : Quiver.Path (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk X.dimension)
        (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk X.dimension))
      (concreteCubeWord_vertex (𝟙 X))
    exact h
  map_comp f g := by
    have hv : (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor.map (concreteCubeWord (f ≫ g))).val =
        (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor.map ((concreteCubeWord f).comp (concreteCubeWord g))).val := by
      rw [concreteCubeWord_vertex]
      erw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor_comp]
      change g.val ∘ f.val =
        (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor.map (concreteCubeWord g)).val ∘
          (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor.map (concreteCubeWord f)).val
      rw [concreteCubeWord_vertex, concreteCubeWord_vertex]
      rfl
    exact (serreCubeWordFunctor_eq_of_vertex_eq A _ _ hv).trans
      ((serreCubeWordFunctor A).map_comp _ _)

/-- 具体的立方体圏の関手は、元の全生成語の Serre 評価を厳密に回収する。 -/
lemma serreConcreteCubeFunctor_map_word {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWords} (p : X ⟶ Y) :
    (serreConcreteCubeFunctor A).map (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor.map p) =
      (serreCubeWordFunctor A).map p :=
  serreCubeWordFunctor_eq_of_vertex_eq A _ p (concreteCubeWord_vertex _)

/-- 具体的な面の像は、元の同じ座標の Serre 面。 -/
lemma serreConcreteCubeFunctor_face (b : Bool) (n : ℕ) (i : Fin (n + 1)) :
    (serreConcreteCubeFunctor A).map (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeFace b n i) = serreCubeFace A b n i := by
  exact (serreConcreteCubeFunctor_map_word A
    (show _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk n ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk (n + 1) from
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeGenerator.face b n i).toPath).trans (serreCubeWordFunctor_face A b n i)

/-- 具体的な削除の像は、元の同じ座標の Serre 退化。 -/
lemma serreConcreteCubeFunctor_degeneracy (n : ℕ) (i : Fin (n + 1)) :
    (serreConcreteCubeFunctor A).map (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeDegeneracy n i) =
      serreCubeDegeneracy A n i := by
  exact (serreConcreteCubeFunctor_map_word A
    (show _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk (n + 1) ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk n from
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeGenerator.degeneracy n i).toPath).trans (serreCubeWordFunctor_degeneracy A n i)

/-- 具体的な max の像は、元の同じ座標の Serre connection。 -/
lemma serreConcreteCubeFunctor_connection (n : ℕ) (i : Fin (n + 1)) :
    (serreConcreteCubeFunctor A).map (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeConnection n i) =
      serreCubeConnection A n i := by
  exact (serreConcreteCubeFunctor_map_word A
    (show _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk (n + 2) ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk (n + 1) from
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeGenerator.connection n i).toPath).trans (serreCubeWordFunctor_connection A n i)

/-- 元の Serre 鎖写像を持つ、具体的立方体圏上の鎖複体値関手。 -/
def serreConcreteCubeComplexFunctor : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube ⥤ Complex A :=
  serreConcreteCubeFunctor A ⋙ Comon.forget (Complex A)

end SerrePositivity.KST.SConstruction
