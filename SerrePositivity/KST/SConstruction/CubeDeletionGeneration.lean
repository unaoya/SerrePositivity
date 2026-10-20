module
public import SerrePositivity.KST.SConstruction.CubeCoordinateSelection

/-! # 順序を保つ座標選択の削除のみによる実現
概要：任意の厳密に単調な入力選択を、座標削除だけの合成として実現する。
方針：未使用座標を一つ削除して入力次元で帰納し、全射なら有限順序の恒等性を使う。
規約：面と connection を削除工程に混ぜない。使われ方：有限 max 正規形の入力圧縮。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 元の具体的な関数が、座標削除だけから生成される条件。 -/
inductive CubeDeletionGenerated : {n m : ℕ} → (CubeVertex n → CubeVertex m) → Prop
  | id (n : ℕ) : CubeDeletionGenerated (_root_.id : CubeVertex n → CubeVertex n)
  | degeneracy (n : ℕ) (i : Fin (n + 1)) :
      CubeDeletionGenerated (cubeVertexDegeneracy n i)
  | comp {n m k : ℕ} {f : CubeVertex n → CubeVertex m} {g : CubeVertex m → CubeVertex k}
      (hf : CubeDeletionGenerated f) (hg : CubeDeletionGenerated g) :
      CubeDeletionGenerated (g ∘ f)

/-- 削除だけで生成された元の関数は、元の具体的立方体圏の射。 -/
lemma cubeDeletionGenerated_generated {n m : ℕ} {f : CubeVertex n → CubeVertex m}
    (h : CubeDeletionGenerated f) : CubeMapGenerated f := by
  induction h with
  | id n => exact .id n
  | degeneracy n i => exact .degeneracy n i
  | comp hf hg ihf ihg => exact .comp ihf ihg

/-- 順序を保つ入力座標の選択は、削除だけの合成で実現される。 -/
lemma cubeCoordinateSelect_deletionGenerated {n m : ℕ} (e : Fin m → Fin n)
    (he : StrictMono e) : CubeDeletionGenerated (cubeCoordinateSelect e) := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero =>
      have h : cubeCoordinateSelect e = (_root_.id : CubeVertex 0 → CubeVertex 0) := by
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
      rw [cubeCoordinateSelect_lower e p hp]
      exact .comp (.degeneracy n p)
        (ih _ (cubeCoordinateLower_strictMono e p hp he))

/-- 順序を保つ入力座標の選択は、元の具体的な cubical 生成関数。 -/
lemma cubeCoordinateSelect_generated {n m : ℕ} (e : Fin m → Fin n) (he : StrictMono e) :
    CubeMapGenerated (cubeCoordinateSelect e) :=
  cubeDeletionGenerated_generated (cubeCoordinateSelect_deletionGenerated e he)

end SerrePositivity.KST.SConstruction
