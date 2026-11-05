module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Kan.CubeSupportComposition
public import Mathlib.CategoryTheory.PathCategory.Basic

/-! # 立方体の生成射の語と具体的な評価
概要：二端点挿入・削除・隣接 max の自由な語と、具体的な立方体への評価を作る。
方針：生成射の quiver に既存の path 圏を適用する。
規約：語の同一視はまだ行わない。使われ方：具体的な射への全射性と Serre 評価の降下。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Kan
open SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 次元を指定した三種の cubical 生成射。 -/
inductive CubeGenerator : ℕ → ℕ → Type
  | face (b : Bool) (n : ℕ) (i : Fin (n + 1)) : _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator n (n + 1)
  | degeneracy (n : ℕ) (i : Fin (n + 1)) : _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator (n + 1) n
  | connection (n : ℕ) (i : Fin (n + 1)) : _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator (n + 2) (n + 1)

/-- 自由な生成語の端点。具体的な立方体圏の quiver と区別する。 -/
structure CubeWordObject where
  dimension : ℕ

/-- 端点間の辺は元の cubical 生成射。 -/
instance cubeGeneratorQuiver : Quiver _root_.SerrePositivity.InfinityCategories.Kan.CubeWordObject where
  Hom X Y := _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator X.dimension Y.dimension

/-- 生成射を有限回合成した自由な語の圏。 -/
abbrev CubeWords := Paths _root_.SerrePositivity.InfinityCategories.Kan.CubeWordObject

/-- 元の三種の生成射を、同じ座標の具体的な関数へ送る。 -/
def cubeGeneratorConcretePrefunctor : _root_.SerrePositivity.InfinityCategories.Kan.CubeWordObject ⥤q _root_.SerrePositivity.InfinityCategories.Kan.ConcreteCube where
  obj X := ⟨X.dimension⟩
  map {X Y} f := by
    cases X
    cases Y
    cases f with
    | _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.face b n i => exact _root_.SerrePositivity.InfinityCategories.Kan.concreteCubeFace b _ i
    | _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.degeneracy n i => exact _root_.SerrePositivity.InfinityCategories.Kan.concreteCubeDegeneracy _ i
    | _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.connection n i => exact _root_.SerrePositivity.InfinityCategories.Kan.concreteCubeConnection _ i

/-- 生成語を、元の合成関数を持つ具体的な立方体の射へ評価する関手。 -/
def cubeWordConcreteFunctor : _root_.SerrePositivity.InfinityCategories.Kan.CubeWords ⥤ _root_.SerrePositivity.InfinityCategories.Kan.ConcreteCube :=
  Paths.lift _root_.SerrePositivity.InfinityCategories.Kan.cubeGeneratorConcretePrefunctor

/-- 一文字の語の具体的な評価は元の生成射。 -/
lemma cubeWordConcreteFunctor_generator {X Y : _root_.SerrePositivity.InfinityCategories.Kan.CubeWordObject} (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kan.cubeWordConcreteFunctor.map f.toPath = _root_.SerrePositivity.InfinityCategories.Kan.cubeGeneratorConcretePrefunctor.map f :=
  Paths.lift_toPath _ f

/-- 語の具体的な評価は恒等を厳密に保存する。 -/
lemma cubeWordConcreteFunctor_id (X : _root_.SerrePositivity.InfinityCategories.Kan.CubeWords) :
    _root_.SerrePositivity.InfinityCategories.Kan.cubeWordConcreteFunctor.map (𝟙 X) = 𝟙 (_root_.SerrePositivity.InfinityCategories.Kan.cubeWordConcreteFunctor.obj X) :=
  _root_.SerrePositivity.InfinityCategories.Kan.cubeWordConcreteFunctor.map_id X

/-- 語の具体的な評価は元の関数の合成を保存する。 -/
lemma cubeWordConcreteFunctor_comp {X Y Z : _root_.SerrePositivity.InfinityCategories.Kan.CubeWords} (f : X ⟶ Y) (g : Y ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.Kan.cubeWordConcreteFunctor.map (f ≫ g) =
      _root_.SerrePositivity.InfinityCategories.Kan.cubeWordConcreteFunctor.map f ≫ _root_.SerrePositivity.InfinityCategories.Kan.cubeWordConcreteFunctor.map g :=
  _root_.SerrePositivity.InfinityCategories.Kan.cubeWordConcreteFunctor.map_comp f g

end SerrePositivity.InfinityCategories.Kan

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeGenerator := _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeWordObject (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeWordObject := _root_.SerrePositivity.InfinityCategories.Kan.CubeWordObject

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeWords (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeWords := _root_.SerrePositivity.InfinityCategories.Kan.CubeWords

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.cubeGeneratorConcretePrefunctor (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeGeneratorConcretePrefunctor := _root_.SerrePositivity.InfinityCategories.Kan.cubeGeneratorConcretePrefunctor

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.cubeGeneratorQuiver (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeGeneratorQuiver := _root_.SerrePositivity.InfinityCategories.Kan.cubeGeneratorQuiver

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.cubeWordConcreteFunctor (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeWordConcreteFunctor := _root_.SerrePositivity.InfinityCategories.Kan.cubeWordConcreteFunctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeWordConcreteFunctor_comp := _root_.SerrePositivity.InfinityCategories.Kan.cubeWordConcreteFunctor_comp

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeWordConcreteFunctor_generator := _root_.SerrePositivity.InfinityCategories.Kan.cubeWordConcreteFunctor_generator

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeWordConcreteFunctor_id := _root_.SerrePositivity.InfinityCategories.Kan.cubeWordConcreteFunctor_id

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeGenerator._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeGenerator._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeGenerator.casesOn := _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.connection (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeGenerator.connection := _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.connection

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.ctorElim (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeGenerator.ctorElim := _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.ctorElim

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.ctorElimType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeGenerator.ctorElimType := _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.ctorElimType

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeGenerator.ctorIdx := _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.ctorIdx

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.degeneracy (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeGenerator.degeneracy := _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.degeneracy

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.face (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeGenerator.face := _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.face

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeGenerator.noConfusion := _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeGenerator.noConfusionType := _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeGenerator.rec := _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeGenerator.recOn := _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.recOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeWordObject._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeWordObject._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Kan.CubeWordObject._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeWordObject._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeWordObject._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Kan.CubeWordObject._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeWordObject.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeWordObject.casesOn := _root_.SerrePositivity.InfinityCategories.Kan.CubeWordObject.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeWordObject.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeWordObject.ctorIdx := _root_.SerrePositivity.InfinityCategories.Kan.CubeWordObject.ctorIdx

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeWordObject.dimension (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeWordObject.dimension := _root_.SerrePositivity.InfinityCategories.Kan.CubeWordObject.dimension

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeWordObject.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeWordObject.mk := _root_.SerrePositivity.InfinityCategories.Kan.CubeWordObject.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeWordObject.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeWordObject.noConfusion := _root_.SerrePositivity.InfinityCategories.Kan.CubeWordObject.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeWordObject.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeWordObject.noConfusionType := _root_.SerrePositivity.InfinityCategories.Kan.CubeWordObject.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeWordObject.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeWordObject.rec := _root_.SerrePositivity.InfinityCategories.Kan.CubeWordObject.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeWordObject.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeWordObject.recOn := _root_.SerrePositivity.InfinityCategories.Kan.CubeWordObject.recOn

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeGeneratorConcretePrefunctor._proof_1 := _root_.SerrePositivity.InfinityCategories.Kan.cubeGeneratorConcretePrefunctor._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeGeneratorConcretePrefunctor._proof_2 := _root_.SerrePositivity.InfinityCategories.Kan.cubeGeneratorConcretePrefunctor._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeGeneratorConcretePrefunctor._proof_3 := _root_.SerrePositivity.InfinityCategories.Kan.cubeGeneratorConcretePrefunctor._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeGeneratorConcretePrefunctor._proof_4 := _root_.SerrePositivity.InfinityCategories.Kan.cubeGeneratorConcretePrefunctor._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeGeneratorConcretePrefunctor._proof_5 := _root_.SerrePositivity.InfinityCategories.Kan.cubeGeneratorConcretePrefunctor._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeGeneratorConcretePrefunctor._proof_6 := _root_.SerrePositivity.InfinityCategories.Kan.cubeGeneratorConcretePrefunctor._proof_6

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.connection.elim (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeGenerator.connection.elim := _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.connection.elim

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeGenerator.connection.inj := _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.connection.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeGenerator.connection.injEq := _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.connection.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.connection.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeGenerator.connection.noConfusion := _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.connection.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeGenerator.connection.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.connection.sizeOf_spec

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.degeneracy.elim (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeGenerator.degeneracy.elim := _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.degeneracy.elim

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeGenerator.degeneracy.inj := _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.degeneracy.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeGenerator.degeneracy.injEq := _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.degeneracy.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.degeneracy.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeGenerator.degeneracy.noConfusion := _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.degeneracy.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeGenerator.degeneracy.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.degeneracy.sizeOf_spec

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.face.elim (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeGenerator.face.elim := _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.face.elim

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeGenerator.face.inj := _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.face.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeGenerator.face.injEq := _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.face.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.face.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeGenerator.face.noConfusion := _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.face.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeGenerator.face.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.face.sizeOf_spec

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeWordObject.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeWordObject.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Kan.CubeWordObject.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeWordObject.mk.inj := _root_.SerrePositivity.InfinityCategories.Kan.CubeWordObject.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeWordObject.mk.injEq := _root_.SerrePositivity.InfinityCategories.Kan.CubeWordObject.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeWordObject.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeWordObject.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Kan.CubeWordObject.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeWordObject.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Kan.CubeWordObject.mk.sizeOf_spec
