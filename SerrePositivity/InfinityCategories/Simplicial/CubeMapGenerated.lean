module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Simplicial.CubeVertexMaps
public import Mathlib.Order.Hom.Basic

/-! # 元の具体的な生成射による立方体の射
概要：頂点集合の間の関数が二端点挿入・削除・隣接 max から生成される条件を定義する。
方針：恒等と合成で閉じた帰納的な条件を置き、join 保存と単調性を帰納する。
規約：射の同一性は元の関数の等号。使われ方：具体的な立方体圏と語の正規形の比較。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Simplicial
open SerrePositivity.KST.SConstruction

/-- 元の頂点関数が正の connection を持つ cubical 生成射の合成である条件。 -/
inductive CubeMapGenerated : {n m : ℕ} → (_root_.SerrePositivity.InfinityCategories.Simplicial.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Simplicial.CubeVertex m) → Prop
  | id (n : ℕ) : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated (_root_.id : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Simplicial.CubeVertex n)
  | face (b : Bool) (n : ℕ) (i : Fin (n + 1)) : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated (_root_.SerrePositivity.InfinityCategories.Simplicial.cubeVertexFace b n i)
  | degeneracy (n : ℕ) (i : Fin (n + 1)) : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated (_root_.SerrePositivity.InfinityCategories.Simplicial.cubeVertexDegeneracy n i)
  | connection (n : ℕ) (i : Fin (n + 1)) : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated (_root_.SerrePositivity.InfinityCategories.Simplicial.cubeVertexConnection n i)
  | comp {n m k : ℕ} {f : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Simplicial.CubeVertex m} {g : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeVertex m → _root_.SerrePositivity.InfinityCategories.Simplicial.CubeVertex k}
      (hf : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated f) (hg : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated g) : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated (g ∘ f)

/-- 元の生成射の任意の合成は、全頂点の pointwise join を保つ。 -/
lemma cubeMapGenerated_sup {n m : ℕ} {f : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Simplicial.CubeVertex m}
    (h : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated f) (x y : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeVertex n) : f (x ⊔ y) = f x ⊔ f y := by
  induction h with
  | _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated.id => rfl
  | _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated.face b n i => exact _root_.SerrePositivity.InfinityCategories.Simplicial.cubeVertexFace_sup b n i x y
  | _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated.degeneracy n i => exact _root_.SerrePositivity.InfinityCategories.Simplicial.cubeVertexDegeneracy_sup n i x y
  | _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated.connection n i => exact _root_.SerrePositivity.InfinityCategories.Simplicial.cubeVertexConnection_sup n i x y
  | _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated.comp hf hg ihf ihg => simp only [Function.comp_apply, ihf, ihg]

/-- 元の生成射の任意の合成は、具体的な立方体の順序を保つ。 -/
lemma cubeMapGenerated_monotone {n m : ℕ} {f : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Simplicial.CubeVertex m}
    (h : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated f) : Monotone f := by
  intro x y hxy
  apply sup_eq_right.mp
  exact (_root_.SerrePositivity.InfinityCategories.Simplicial.cubeMapGenerated_sup h x y).symm.trans (congrArg f (sup_eq_right.mpr hxy))

/-- 元の具体的な射を同じ頂点関数を持つ単調写像へ束ねる。 -/
def cubeMapGeneratedOrderHom {n m : ℕ} {f : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Simplicial.CubeVertex m}
    (h : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated f) : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeVertex n →o _root_.SerrePositivity.InfinityCategories.Simplicial.CubeVertex m where
  toFun := f
  monotone' := _root_.SerrePositivity.InfinityCategories.Simplicial.cubeMapGenerated_monotone h

end SerrePositivity.InfinityCategories.Simplicial

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeMapGenerated := _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated.below (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeMapGenerated.below := _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated.below

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.cubeMapGeneratedOrderHom (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeMapGeneratedOrderHom := _root_.SerrePositivity.InfinityCategories.Simplicial.cubeMapGeneratedOrderHom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeMapGenerated_monotone := _root_.SerrePositivity.InfinityCategories.Simplicial.cubeMapGenerated_monotone

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeMapGenerated_sup := _root_.SerrePositivity.InfinityCategories.Simplicial.cubeMapGenerated_sup

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeMapGenerated.brecOn := _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated.brecOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeMapGenerated.casesOn := _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated.comp (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeMapGenerated.comp := _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated.comp

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated.connection (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeMapGenerated.connection := _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated.connection

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated.degeneracy (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeMapGenerated.degeneracy := _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated.degeneracy

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated.face (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeMapGenerated.face := _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated.face

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated.id (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeMapGenerated.id := _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated.id

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeMapGenerated.rec := _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeMapGenerated.recOn := _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated.recOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated.below.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeMapGenerated.below.casesOn := _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated.below.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated.below.comp (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeMapGenerated.below.comp := _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated.below.comp

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated.below.connection (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeMapGenerated.below.connection := _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated.below.connection

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated.below.degeneracy (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeMapGenerated.below.degeneracy := _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated.below.degeneracy

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated.below.face (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeMapGenerated.below.face := _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated.below.face

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated.below.id (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeMapGenerated.below.id := _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated.below.id

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated.below.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeMapGenerated.below.rec := _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated.below.rec
