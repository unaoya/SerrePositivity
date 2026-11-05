module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Kan.KanMappingComposition

/-! # 指定した三つの合成面を全体として保持する三射の四面体
概要：三射の既存の三つの実合成面を同じ四面体の面に保持する。
方針：共有辺を厳密に持つ三つの合成面から第一内ホーンを貼り、残る実面を取り出す。
規約：全三面を保持する。得られる第四面と独立に指定した第四面の一致は主張しない。
使われ方：三入力の元の合成面を保持し、残る高次整合性の比較対象を得る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Kan
open SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped _root_.Simplicial

/-- 長辺の表示を移し、元の全二単体の等号を同じデータに保存する。 -/
def compositionTriangleLongEdgeData {E : SSet.{u}} {x y z : E _⦋0⦌}
    {a : E.Edge x y} {b : E.Edge y z} {c d : E.Edge x z}
    (T : SSet.Edge.CompStruct a b c) (hc : c.edge = d.edge) :
    {T' : SSet.Edge.CompStruct a b d // T'.simplex = T.simplex} :=
  ⟨T.ofEq rfl rfl hc, rfl⟩

/-- 指定した三つの実合成面を保持する実四面体と残る第四面。 -/
structure CompositionTripleTetrahedron {E : SSet.{u}} {w x y z : E _⦋0⦌}
    {a : E.Edge w x} {b : E.Edge x y} {c : E.Edge y z}
    {ab : E.Edge w y} {bc : E.Edge x z} {abc : E.Edge w z}
    (first : SSet.Edge.CompStruct a b ab)
    (second : SSet.Edge.CompStruct b c bc)
    (right : SSet.Edge.CompStruct a bc abc) where
  /-- 指定三面を持つ同じ実三単体。 -/
  simplex : E _⦋3⦌
  /-- 後の二射の元の全合成面。 -/
  second_face : E.δ 0 simplex = second.simplex
  /-- 右結合の元の全合成面。 -/
  right_face : E.δ 2 simplex = right.simplex
  /-- 前の二射の元の全合成面。 -/
  first_face : E.δ 3 simplex = first.simplex
  /-- 同じ四面体の左結合の実合成面。 -/
  left : SSet.Edge.CompStruct ab c abc
  /-- 第四面は新たな実三角形そのもの。 -/
  left_face : left.simplex = E.δ 1 simplex

/-- 元の全三面を持つ指定済みの全三単体を、同じ実結合替えデータとして回収する。 -/
def compositionTripleTetrahedronOfMap {E : SSet.{u}}
    {w x y z : E _⦋0⦌} {a : E.Edge w x} {b : E.Edge x y} {c : E.Edge y z}
    {ab : E.Edge w y} {bc : E.Edge x z} {abc : E.Edge w z}
    (first : SSet.Edge.CompStruct a b ab)
    (second : SSet.Edge.CompStruct b c bc)
    (right : SSet.Edge.CompStruct a bc abc)
    (s : (Δ[3] : SSet.{u}) ⟶ E)
    (hs₀ : stdSimplex.δ 0 ≫ s = SSet.yonedaEquiv.symm second.simplex)
    (hs₂ : stdSimplex.δ 2 ≫ s = SSet.yonedaEquiv.symm right.simplex)
    (hs₃ : stdSimplex.δ 3 ≫ s = SSet.yonedaEquiv.symm first.simplex)
    : _root_.SerrePositivity.InfinityCategories.Kan.CompositionTripleTetrahedron first second right := by
  let σ := SSet.yonedaEquiv s
  have h₀ : E.δ 0 σ = second.simplex := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hs₀, Equiv.apply_symm_apply]
  have h₂ : E.δ 2 σ = right.simplex := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hs₂, Equiv.apply_symm_apply]
  have h₃ : E.δ 3 σ = first.simplex := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hs₃, Equiv.apply_symm_apply]
  let T : SSet.Edge.CompStruct ab c abc := SSet.Edge.CompStruct.mk (E.δ 1 σ)
    (SSet.yonedaEquiv.symm.injective (by
      simp [σ, ← stdSimplex.δ_comp_yonedaEquiv_symm,
        ← dsimp% stdSimplex.δ_comp_δ_assoc (n := 1) (i := 1) (j := 2) (by simp), hs₃]))
    (SSet.yonedaEquiv.symm.injective (by
      simp [σ, ← stdSimplex.δ_comp_yonedaEquiv_symm,
        dsimp% stdSimplex.δ_comp_δ_assoc (n := 1) (i := 0) (j := 0) (by simp), hs₀]))
    (SSet.yonedaEquiv.symm.injective (by
      simp [σ, ← stdSimplex.δ_comp_yonedaEquiv_symm,
        dsimp% stdSimplex.δ_comp_δ_self_assoc (i := 1), hs₂]))
  exact ⟨σ, h₀, h₂, h₃, T, rfl⟩

/-- 元の三つの全合成面を保つ実四面体から、左結合の実合成面を得る。 -/
def compositionTripleTetrahedron {E : SSet.{u}} [Quasicategory E]
    {w x y z : E _⦋0⦌} {a : E.Edge w x} {b : E.Edge x y} {c : E.Edge y z}
    {ab : E.Edge w y} {bc : E.Edge x z} {abc : E.Edge w z}
    (first : SSet.Edge.CompStruct a b ab)
    (second : SSet.Edge.CompStruct b c bc)
    (right : SSet.Edge.CompStruct a bc abc) :
    _root_.SerrePositivity.InfinityCategories.Kan.CompositionTripleTetrahedron first second right := by
  let horn := horn₃₁.exists_desc (SSet.yonedaEquiv.symm second.simplex)
    (SSet.yonedaEquiv.symm right.simplex) (SSet.yonedaEquiv.symm first.simplex)
    (by simp) (by simp) (by simp)
  let fill := Quasicategory.hornFilling (by decide) (by decide) horn.choose
  let s := fill.choose
  have hs₀ : stdSimplex.δ 0 ≫ s = SSet.yonedaEquiv.symm second.simplex := by
    have he := congrArg (· ≫ s) (SSet.horn.ι_ι (1 : Fin 4) 0 (by decide)).symm
    exact he.trans ((Category.assoc _ _ _).trans
      ((congrArg (SSet.horn.ι (1 : Fin 4) 0 (by decide) ≫ ·) fill.choose_spec.symm).trans
        horn.choose_spec.1))
  have hs₂ : stdSimplex.δ 2 ≫ s = SSet.yonedaEquiv.symm right.simplex := by
    have he := congrArg (· ≫ s) (SSet.horn.ι_ι (1 : Fin 4) 2 (by decide)).symm
    exact he.trans ((Category.assoc _ _ _).trans
      ((congrArg (SSet.horn.ι (1 : Fin 4) 2 (by decide) ≫ ·) fill.choose_spec.symm).trans
        horn.choose_spec.2.1))
  have hs₃ : stdSimplex.δ 3 ≫ s = SSet.yonedaEquiv.symm first.simplex := by
    have he := congrArg (· ≫ s) (SSet.horn.ι_ι (1 : Fin 4) 3 (by decide)).symm
    exact he.trans ((Category.assoc _ _ _).trans
      ((congrArg (SSet.horn.ι (1 : Fin 4) 3 (by decide) ≫ ·) fill.choose_spec.symm).trans
        horn.choose_spec.2.2))
  exact _root_.SerrePositivity.InfinityCategories.Kan.compositionTripleTetrahedronOfMap first second right s hs₀ hs₂ hs₃

end SerrePositivity.InfinityCategories.Kan

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CompositionTripleTetrahedron (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CompositionTripleTetrahedron := _root_.SerrePositivity.InfinityCategories.Kan.CompositionTripleTetrahedron

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.compositionTriangleLongEdgeData (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.compositionTriangleLongEdgeData := _root_.SerrePositivity.InfinityCategories.Kan.compositionTriangleLongEdgeData

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.compositionTripleTetrahedron (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.compositionTripleTetrahedron := _root_.SerrePositivity.InfinityCategories.Kan.compositionTripleTetrahedron

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.compositionTripleTetrahedronOfMap (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.compositionTripleTetrahedronOfMap := _root_.SerrePositivity.InfinityCategories.Kan.compositionTripleTetrahedronOfMap

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CompositionTripleTetrahedron._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CompositionTripleTetrahedron._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Kan.CompositionTripleTetrahedron._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CompositionTripleTetrahedron._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CompositionTripleTetrahedron._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Kan.CompositionTripleTetrahedron._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CompositionTripleTetrahedron.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CompositionTripleTetrahedron.casesOn := _root_.SerrePositivity.InfinityCategories.Kan.CompositionTripleTetrahedron.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CompositionTripleTetrahedron.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CompositionTripleTetrahedron.ctorIdx := _root_.SerrePositivity.InfinityCategories.Kan.CompositionTripleTetrahedron.ctorIdx

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CompositionTripleTetrahedron.first_face := _root_.SerrePositivity.InfinityCategories.Kan.CompositionTripleTetrahedron.first_face

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CompositionTripleTetrahedron.left (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CompositionTripleTetrahedron.left := _root_.SerrePositivity.InfinityCategories.Kan.CompositionTripleTetrahedron.left

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CompositionTripleTetrahedron.left_face := _root_.SerrePositivity.InfinityCategories.Kan.CompositionTripleTetrahedron.left_face

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CompositionTripleTetrahedron.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CompositionTripleTetrahedron.mk := _root_.SerrePositivity.InfinityCategories.Kan.CompositionTripleTetrahedron.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CompositionTripleTetrahedron.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CompositionTripleTetrahedron.noConfusion := _root_.SerrePositivity.InfinityCategories.Kan.CompositionTripleTetrahedron.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CompositionTripleTetrahedron.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CompositionTripleTetrahedron.noConfusionType := _root_.SerrePositivity.InfinityCategories.Kan.CompositionTripleTetrahedron.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CompositionTripleTetrahedron.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CompositionTripleTetrahedron.rec := _root_.SerrePositivity.InfinityCategories.Kan.CompositionTripleTetrahedron.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CompositionTripleTetrahedron.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CompositionTripleTetrahedron.recOn := _root_.SerrePositivity.InfinityCategories.Kan.CompositionTripleTetrahedron.recOn

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CompositionTripleTetrahedron.right_face := _root_.SerrePositivity.InfinityCategories.Kan.CompositionTripleTetrahedron.right_face

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CompositionTripleTetrahedron.second_face := _root_.SerrePositivity.InfinityCategories.Kan.CompositionTripleTetrahedron.second_face

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CompositionTripleTetrahedron.simplex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CompositionTripleTetrahedron.simplex := _root_.SerrePositivity.InfinityCategories.Kan.CompositionTripleTetrahedron.simplex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.compositionTriangleLongEdgeData._proof_1 := _root_.SerrePositivity.InfinityCategories.Kan.compositionTriangleLongEdgeData._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.compositionTriangleLongEdgeData._proof_2 := _root_.SerrePositivity.InfinityCategories.Kan.compositionTriangleLongEdgeData._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.compositionTripleTetrahedron._proof_1 := _root_.SerrePositivity.InfinityCategories.Kan.compositionTripleTetrahedron._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.compositionTripleTetrahedron._proof_10 := _root_.SerrePositivity.InfinityCategories.Kan.compositionTripleTetrahedron._proof_10

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.compositionTripleTetrahedron._proof_11 := _root_.SerrePositivity.InfinityCategories.Kan.compositionTripleTetrahedron._proof_11

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.compositionTripleTetrahedron._proof_12 := _root_.SerrePositivity.InfinityCategories.Kan.compositionTripleTetrahedron._proof_12

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.compositionTripleTetrahedron._proof_13 := _root_.SerrePositivity.InfinityCategories.Kan.compositionTripleTetrahedron._proof_13

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.compositionTripleTetrahedron._proof_14 := _root_.SerrePositivity.InfinityCategories.Kan.compositionTripleTetrahedron._proof_14

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.compositionTripleTetrahedron._proof_2 := _root_.SerrePositivity.InfinityCategories.Kan.compositionTripleTetrahedron._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.compositionTripleTetrahedron._proof_3 := _root_.SerrePositivity.InfinityCategories.Kan.compositionTripleTetrahedron._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.compositionTripleTetrahedron._proof_4 := _root_.SerrePositivity.InfinityCategories.Kan.compositionTripleTetrahedron._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.compositionTripleTetrahedron._proof_5 := _root_.SerrePositivity.InfinityCategories.Kan.compositionTripleTetrahedron._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.compositionTripleTetrahedron._proof_6 := _root_.SerrePositivity.InfinityCategories.Kan.compositionTripleTetrahedron._proof_6

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.compositionTripleTetrahedron._proof_7 := _root_.SerrePositivity.InfinityCategories.Kan.compositionTripleTetrahedron._proof_7

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.compositionTripleTetrahedron._proof_8 := _root_.SerrePositivity.InfinityCategories.Kan.compositionTripleTetrahedron._proof_8

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.compositionTripleTetrahedron._proof_9 := _root_.SerrePositivity.InfinityCategories.Kan.compositionTripleTetrahedron._proof_9

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.compositionTripleTetrahedronOfMap._proof_1 := _root_.SerrePositivity.InfinityCategories.Kan.compositionTripleTetrahedronOfMap._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.compositionTripleTetrahedronOfMap._proof_10 := _root_.SerrePositivity.InfinityCategories.Kan.compositionTripleTetrahedronOfMap._proof_10

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.compositionTripleTetrahedronOfMap._proof_11 := _root_.SerrePositivity.InfinityCategories.Kan.compositionTripleTetrahedronOfMap._proof_11

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.compositionTripleTetrahedronOfMap._proof_12 := _root_.SerrePositivity.InfinityCategories.Kan.compositionTripleTetrahedronOfMap._proof_12

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.compositionTripleTetrahedronOfMap._proof_2 := _root_.SerrePositivity.InfinityCategories.Kan.compositionTripleTetrahedronOfMap._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.compositionTripleTetrahedronOfMap._proof_3 := _root_.SerrePositivity.InfinityCategories.Kan.compositionTripleTetrahedronOfMap._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.compositionTripleTetrahedronOfMap._proof_4 := _root_.SerrePositivity.InfinityCategories.Kan.compositionTripleTetrahedronOfMap._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.compositionTripleTetrahedronOfMap._proof_5 := _root_.SerrePositivity.InfinityCategories.Kan.compositionTripleTetrahedronOfMap._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.compositionTripleTetrahedronOfMap._proof_6 := _root_.SerrePositivity.InfinityCategories.Kan.compositionTripleTetrahedronOfMap._proof_6

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.compositionTripleTetrahedronOfMap._proof_7 := _root_.SerrePositivity.InfinityCategories.Kan.compositionTripleTetrahedronOfMap._proof_7

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.compositionTripleTetrahedronOfMap._proof_8 := _root_.SerrePositivity.InfinityCategories.Kan.compositionTripleTetrahedronOfMap._proof_8

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.compositionTripleTetrahedronOfMap._proof_9 := _root_.SerrePositivity.InfinityCategories.Kan.compositionTripleTetrahedronOfMap._proof_9

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CompositionTripleTetrahedron.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CompositionTripleTetrahedron.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Kan.CompositionTripleTetrahedron.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CompositionTripleTetrahedron.mk.inj := _root_.SerrePositivity.InfinityCategories.Kan.CompositionTripleTetrahedron.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CompositionTripleTetrahedron.mk.injEq := _root_.SerrePositivity.InfinityCategories.Kan.CompositionTripleTetrahedron.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CompositionTripleTetrahedron.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CompositionTripleTetrahedron.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Kan.CompositionTripleTetrahedron.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CompositionTripleTetrahedron.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Kan.CompositionTripleTetrahedron.mk.sizeOf_spec
