module
public import SerrePositivity.InfinityCategories.Kan.CubeSupportComposition
public import Mathlib.CategoryTheory.PathCategory.Basic

/-! # 立方体の生成射の語と具体的な評価
概要：二端点挿入・削除・隣接 max の自由な語と、具体的な立方体への評価を作る。
方針：生成射の quiver に既存の path 圏を適用する。
規約：語の同一視はまだ行わない。使われ方：具体的な射への全射性と Serre 評価の降下。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 次元を指定した三種の cubical 生成射。 -/
inductive CubeGenerator : ℕ → ℕ → Type
  | face (b : Bool) (n : ℕ) (i : Fin (n + 1)) : CubeGenerator n (n + 1)
  | degeneracy (n : ℕ) (i : Fin (n + 1)) : CubeGenerator (n + 1) n
  | connection (n : ℕ) (i : Fin (n + 1)) : CubeGenerator (n + 2) (n + 1)

/-- 自由な生成語の端点。具体的な立方体圏の quiver と区別する。 -/
structure CubeWordObject where
  dimension : ℕ

/-- 端点間の辺は元の cubical 生成射。 -/
instance cubeGeneratorQuiver : Quiver CubeWordObject where
  Hom X Y := CubeGenerator X.dimension Y.dimension

/-- 生成射を有限回合成した自由な語の圏。 -/
abbrev CubeWords := Paths CubeWordObject

/-- 元の三種の生成射を、同じ座標の具体的な関数へ送る。 -/
def cubeGeneratorConcretePrefunctor : CubeWordObject ⥤q ConcreteCube where
  obj X := ⟨X.dimension⟩
  map {X Y} f := by
    cases X
    cases Y
    cases f with
    | face b n i => exact concreteCubeFace b _ i
    | degeneracy n i => exact concreteCubeDegeneracy _ i
    | connection n i => exact concreteCubeConnection _ i

/-- 生成語を、元の合成関数を持つ具体的な立方体の射へ評価する関手。 -/
def cubeWordConcreteFunctor : CubeWords ⥤ ConcreteCube :=
  Paths.lift cubeGeneratorConcretePrefunctor

/-- 一文字の語の具体的な評価は元の生成射。 -/
lemma cubeWordConcreteFunctor_generator {X Y : CubeWordObject} (f : X ⟶ Y) :
    cubeWordConcreteFunctor.map f.toPath = cubeGeneratorConcretePrefunctor.map f :=
  Paths.lift_toPath _ f

/-- 語の具体的な評価は恒等を厳密に保存する。 -/
lemma cubeWordConcreteFunctor_id (X : CubeWords) :
    cubeWordConcreteFunctor.map (𝟙 X) = 𝟙 (cubeWordConcreteFunctor.obj X) :=
  cubeWordConcreteFunctor.map_id X

/-- 語の具体的な評価は元の関数の合成を保存する。 -/
lemma cubeWordConcreteFunctor_comp {X Y Z : CubeWords} (f : X ⟶ Y) (g : Y ⟶ Z) :
    cubeWordConcreteFunctor.map (f ≫ g) =
      cubeWordConcreteFunctor.map f ≫ cubeWordConcreteFunctor.map g :=
  cubeWordConcreteFunctor.map_comp f g

end SerrePositivity.KST.SConstruction
