module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertexMaps
public import Mathlib.Order.Hom.Basic

/-! # 元の具体的な生成射による立方体の射
概要：頂点集合の間の関数が二端点挿入・削除・隣接 max から生成される条件を定義する。
方針：恒等と合成で閉じた帰納的な条件を置き、join 保存と単調性を帰納する。
規約：射の同一性は元の関数の等号。使われ方：具体的な立方体圏と語の正規形の比較。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction

/-- 元の頂点関数が正の connection を持つ cubical 生成射の合成である条件。 -/
inductive CubeMapGenerated : {n m : ℕ} → (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m) → Prop
  | id (n : ℕ) : CubeMapGenerated (_root_.id : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n)
  | face (b : Bool) (n : ℕ) (i : Fin (n + 1)) : CubeMapGenerated (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace b n i)
  | degeneracy (n : ℕ) (i : Fin (n + 1)) : CubeMapGenerated (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy n i)
  | connection (n : ℕ) (i : Fin (n + 1)) : CubeMapGenerated (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection n i)
  | comp {n m k : ℕ} {f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m} {g : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex k}
      (hf : CubeMapGenerated f) (hg : CubeMapGenerated g) : CubeMapGenerated (g ∘ f)

/-- 元の生成射の任意の合成は、全頂点の pointwise join を保つ。 -/
lemma cubeMapGenerated_sup {n m : ℕ} {f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m}
    (h : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated f) (x y : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n) : f (x ⊔ y) = f x ⊔ f y := by
  induction h with
  | id => rfl
  | face b n i => exact _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace_sup b n i x y
  | degeneracy n i => exact _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy_sup n i x y
  | connection n i => exact _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection_sup n i x y
  | comp hf hg ihf ihg => simp only [Function.comp_apply, ihf, ihg]

/-- 元の生成射の任意の合成は、具体的な立方体の順序を保つ。 -/
lemma cubeMapGenerated_monotone {n m : ℕ} {f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m}
    (h : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated f) : Monotone f := by
  intro x y hxy
  apply sup_eq_right.mp
  exact (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeMapGenerated_sup h x y).symm.trans (congrArg f (sup_eq_right.mpr hxy))

/-- 元の具体的な射を同じ頂点関数を持つ単調写像へ束ねる。 -/
def cubeMapGeneratedOrderHom {n m : ℕ} {f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m}
    (h : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated f) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n →o _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m where
  toFun := f
  monotone' := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeMapGenerated_monotone h

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeMapGenerated := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated.below (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeMapGenerated.below := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated.below

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeMapGeneratedOrderHom (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeMapGeneratedOrderHom := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeMapGeneratedOrderHom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeMapGenerated_monotone := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeMapGenerated_monotone

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeMapGenerated_sup := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeMapGenerated_sup

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeMapGenerated.brecOn := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated.brecOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeMapGenerated.casesOn := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated.comp (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeMapGenerated.comp := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated.comp

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated.connection (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeMapGenerated.connection := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated.connection

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated.degeneracy (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeMapGenerated.degeneracy := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated.degeneracy

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated.face (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeMapGenerated.face := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated.face

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated.id (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeMapGenerated.id := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated.id

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeMapGenerated.rec := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeMapGenerated.recOn := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated.recOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated.below.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeMapGenerated.below.casesOn := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated.below.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated.below.comp (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeMapGenerated.below.comp := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated.below.comp

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated.below.connection (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeMapGenerated.below.connection := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated.below.connection

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated.below.degeneracy (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeMapGenerated.below.degeneracy := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated.below.degeneracy

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated.below.face (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeMapGenerated.below.face := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated.below.face

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated.below.id (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeMapGenerated.below.id := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated.below.id

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated.below.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeMapGenerated.below.rec := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated.below.rec
