module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeCoordinateSelection

/-! # 順序を保つ座標選択の削除のみによる実現
概要：任意の厳密に単調な入力選択を、座標削除だけの合成として実現する。
方針：未使用座標を一つ削除して入力次元で帰納し、全射なら有限順序の恒等性を使う。
規約：面と connection を削除工程に混ぜない。使われ方：有限 max 正規形の入力圧縮。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.SConstruction

/-- 元の具体的な関数が、座標削除だけから生成される条件。 -/
inductive CubeDeletionGenerated : {n m : ℕ} → (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m) → Prop
  | id (n : ℕ) : CubeDeletionGenerated (_root_.id : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n)
  | degeneracy (n : ℕ) (i : Fin (n + 1)) :
      CubeDeletionGenerated (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy n i)
  | comp {n m k : ℕ} {f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m} {g : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex k}
      (hf : CubeDeletionGenerated f) (hg : CubeDeletionGenerated g) :
      CubeDeletionGenerated (g ∘ f)

/-- 削除だけで生成された元の関数は、元の具体的立方体圏の射。 -/
lemma cubeDeletionGenerated_generated {n m : ℕ} {f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m}
    (h : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionGenerated f) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated f := by
  induction h with
  | id n => exact .id n
  | degeneracy n i => exact .degeneracy n i
  | comp hf hg ihf ihg => exact .comp ihf ihg

/-- 順序を保つ入力座標の選択は、削除だけの合成で実現される。 -/
lemma cubeCoordinateSelect_deletionGenerated {n m : ℕ} (e : Fin m → Fin n)
    (he : StrictMono e) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionGenerated (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateSelect e) := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero =>
      have h : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateSelect e = (_root_.id : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex 0 → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex 0) := by
        funext x j
        exact Fin.elim0 j
      rw [h]
      exact .id 0
    | succ m => exact Fin.elim0 (e 0)
  | succ n ih =>
    by_cases hs : Function.Surjective e
    · have hm : m = n + 1 := by
        simpa only [Fintype.card_fin] using Fintype.card_of_bijective ⟨he.injective, hs⟩
      subst m
      rw [he.eq_id]
      exact .id (n + 1)
    · simp only [Function.Surjective, not_forall, not_exists] at hs
      obtain ⟨p, hp⟩ := hs
      rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateSelect_lower e p hp]
      exact .comp (.degeneracy n p)
        (ih _ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateLower_strictMono e p hp he))

/-- 順序を保つ入力座標の選択は、元の具体的な cubical 生成関数。 -/
lemma cubeCoordinateSelect_generated {n m : ℕ} (e : Fin m → Fin n) (he : StrictMono e) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateSelect e) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionGenerated_generated (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateSelect_deletionGenerated e he)

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionGenerated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeDeletionGenerated := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionGenerated

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionGenerated.below (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeDeletionGenerated.below := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionGenerated.below

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeCoordinateSelect_deletionGenerated := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateSelect_deletionGenerated

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeCoordinateSelect_generated := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateSelect_generated

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeDeletionGenerated_generated := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionGenerated_generated

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeDeletionGenerated.brecOn := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionGenerated.brecOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionGenerated.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeDeletionGenerated.casesOn := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionGenerated.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionGenerated.comp (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeDeletionGenerated.comp := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionGenerated.comp

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionGenerated.degeneracy (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeDeletionGenerated.degeneracy := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionGenerated.degeneracy

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionGenerated.id (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeDeletionGenerated.id := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionGenerated.id

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionGenerated.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeDeletionGenerated.rec := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionGenerated.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionGenerated.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeDeletionGenerated.recOn := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionGenerated.recOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionGenerated.below.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeDeletionGenerated.below.casesOn := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionGenerated.below.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionGenerated.below.comp (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeDeletionGenerated.below.comp := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionGenerated.below.comp

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionGenerated.below.degeneracy (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeDeletionGenerated.below.degeneracy := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionGenerated.below.degeneracy

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionGenerated.below.id (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeDeletionGenerated.below.id := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionGenerated.below.id

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionGenerated.below.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeDeletionGenerated.below.rec := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionGenerated.below.rec
