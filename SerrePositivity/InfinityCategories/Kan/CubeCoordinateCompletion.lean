module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Kan.CubeSupportBlockEvaluation

/-! # 指定した定数を保つ出力座標の補完
概要：順序を保つ入力の挿入を、残りの各座標の指定した零・一の定数で補完する。
方針：零埋め挿入に背景頂点を join し、未使用座標の面挿入で帰納する。
規約：使用する座標の背景は零。使われ方：正規化の最後の定数出力挿入。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Kan
open SerrePositivity.KST.SConstruction

/-- 元の具体的な関数が二端点の面だけから生成される条件。 -/
inductive CubeFaceGenerated : {n m : ℕ} → (CubeVertex n → CubeVertex m) → Prop
  | id (n : ℕ) : CubeFaceGenerated (_root_.id : CubeVertex n → CubeVertex n)
  | face (b : Bool) (n : ℕ) (p : Fin (n + 1)) : CubeFaceGenerated (cubeVertexFace b n p)
  | comp {n m k : ℕ} {f : CubeVertex n → CubeVertex m} {g : CubeVertex m → CubeVertex k}
      (hf : CubeFaceGenerated f) (hg : CubeFaceGenerated g) : CubeFaceGenerated (g ∘ f)

/-- 面だけで生成された元の関数は、具体的な立方体圏の射。 -/
lemma cubeFaceGenerated_generated {n m : ℕ} {f : CubeVertex n → CubeVertex m}
    (h : CubeFaceGenerated f) : CubeMapGenerated f := by
  induction h with
  | id n => exact .id n
  | face b n p => exact .face b n p
  | comp hf hg ihf ihg => exact .comp ihf ihg

/-- 選択した座標を元の背景頂点の定数で補完する関数。 -/
def cubeCoordinateComplete {n m : ℕ} (e : Fin m → Fin n) (b : CubeVertex n) :
    CubeVertex m → CubeVertex n :=
  fun x => b ⊔ cubeCoordinateInsert e x

/-- 選択された座標では、背景が零なら元の入力を回収する。 -/
lemma cubeCoordinateComplete_image {n m : ℕ} (e : Fin m → Fin n)
    (he : Function.Injective e) (b : CubeVertex n) (hb : ∀ i, b (e i) = false)
    (x : CubeVertex m) (i : Fin m) : cubeCoordinateComplete e b x (e i) = x i := by
  have h := congrFun (cubeCoordinateSelect_insert e he x) i
  change cubeCoordinateInsert e x (e i) = x i at h
  change b (e i) ⊔ cubeCoordinateInsert e x (e i) = x i
  rw [hb, h]
  exact bot_sup_eq _

/-- 選択されない座標では、元の背景の定数を保つ。 -/
lemma cubeCoordinateComplete_outside {n m : ℕ} (e : Fin m → Fin n) (b : CubeVertex n)
    (x : CubeVertex m) (j : Fin n) (hj : j ∉ Set.range e) :
    cubeCoordinateComplete e b x j = b j := by
  have hi : cubeCoordinateInsert e x j = false := by
    apply Bool.eq_false_iff.mpr
    intro htrue
    obtain ⟨i, hi, _⟩ := (cubeCoordinateInsert_true_iff e x j).mp htrue
    exact hj ⟨i, hi⟩
  change b j ⊔ cubeCoordinateInsert e x j = b j
  rw [hi]
  exact sup_bot_eq _

/-- 一つの未使用座標の定数面を挿入して、元の背景つき補完を回収する。 -/
lemma cubeCoordinateComplete_lower {n m : ℕ} (e : Fin m → Fin (n + 1))
    (p : Fin (n + 1)) (hp : ∀ j, e j ≠ p) (b : CubeVertex (n + 1)) :
    cubeCoordinateComplete e b = cubeVertexFace (b p) n p ∘
      cubeCoordinateComplete (cubeCoordinateLower e p hp) (cubeVertexDegeneracy n p b) := by
  funext x k
  refine Fin.succAboveCases p ?_ (fun k => ?_) k
  · simp [cubeCoordinateComplete, cubeCoordinateInsert_lower e p hp, cubeVertexFace]
  · simp [cubeCoordinateComplete, cubeCoordinateInsert_lower e p hp, cubeVertexFace,
      cubeVertexDegeneracy]

/-- 厳密単調な座標挿入と使用しない座標の定数補完は、元の面から生成される。 -/
lemma cubeCoordinateComplete_faceGenerated {n m : ℕ} (e : Fin m → Fin n)
    (he : StrictMono e) (b : CubeVertex n) (hb : ∀ i, b (e i) = false) :
    CubeFaceGenerated (cubeCoordinateComplete e b) := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero =>
      have h : cubeCoordinateComplete e b = (_root_.id : CubeVertex 0 → CubeVertex 0) := by
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
      have hid : cubeCoordinateComplete e b = (_root_.id : CubeVertex (n + 1) → _) := by
        funext x j
        simpa only [he.eq_id, Function.id_def] using
          cubeCoordinateComplete_image e he.injective b hb x j
      rw [hid]
      exact .id (n + 1)
    · simp only [Function.Surjective, not_forall, not_exists] at hs
      obtain ⟨p, hp⟩ := hs
      rw [cubeCoordinateComplete_lower e p hp]
      apply CubeFaceGenerated.comp
        (ih _ (cubeCoordinateLower_strictMono e p hp he) (cubeVertexDegeneracy n p b) ?_)
        (.face (b p) n p)
      intro j
      change b (p.succAbove (cubeCoordinateLower e p hp j)) = false
      rw [cubeCoordinateLower_spec]
      exact hb j

/-- 背景つきの座標補完は、元の具体的な cubical 生成関数。 -/
lemma cubeCoordinateComplete_generated {n m : ℕ} (e : Fin m → Fin n)
    (he : StrictMono e) (b : CubeVertex n) (hb : ∀ i, b (e i) = false) :
    CubeMapGenerated (cubeCoordinateComplete e b) :=
  cubeFaceGenerated_generated (cubeCoordinateComplete_faceGenerated e he b hb)

end SerrePositivity.InfinityCategories.Kan

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeFaceGenerated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeFaceGenerated := _root_.SerrePositivity.InfinityCategories.Kan.CubeFaceGenerated

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeFaceGenerated.below (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeFaceGenerated.below := _root_.SerrePositivity.InfinityCategories.Kan.CubeFaceGenerated.below

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.cubeCoordinateComplete (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeCoordinateComplete := _root_.SerrePositivity.InfinityCategories.Kan.cubeCoordinateComplete

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeCoordinateComplete_faceGenerated := _root_.SerrePositivity.InfinityCategories.Kan.cubeCoordinateComplete_faceGenerated

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeCoordinateComplete_generated := _root_.SerrePositivity.InfinityCategories.Kan.cubeCoordinateComplete_generated

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeCoordinateComplete_image := _root_.SerrePositivity.InfinityCategories.Kan.cubeCoordinateComplete_image

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeCoordinateComplete_lower := _root_.SerrePositivity.InfinityCategories.Kan.cubeCoordinateComplete_lower

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeCoordinateComplete_outside := _root_.SerrePositivity.InfinityCategories.Kan.cubeCoordinateComplete_outside

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeFaceGenerated_generated := _root_.SerrePositivity.InfinityCategories.Kan.cubeFaceGenerated_generated

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeFaceGenerated.brecOn := _root_.SerrePositivity.InfinityCategories.Kan.CubeFaceGenerated.brecOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeFaceGenerated.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeFaceGenerated.casesOn := _root_.SerrePositivity.InfinityCategories.Kan.CubeFaceGenerated.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeFaceGenerated.comp (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeFaceGenerated.comp := _root_.SerrePositivity.InfinityCategories.Kan.CubeFaceGenerated.comp

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeFaceGenerated.face (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeFaceGenerated.face := _root_.SerrePositivity.InfinityCategories.Kan.CubeFaceGenerated.face

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeFaceGenerated.id (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeFaceGenerated.id := _root_.SerrePositivity.InfinityCategories.Kan.CubeFaceGenerated.id

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeFaceGenerated.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeFaceGenerated.rec := _root_.SerrePositivity.InfinityCategories.Kan.CubeFaceGenerated.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeFaceGenerated.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeFaceGenerated.recOn := _root_.SerrePositivity.InfinityCategories.Kan.CubeFaceGenerated.recOn

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeCoordinateComplete.eq_1 := _root_.SerrePositivity.InfinityCategories.Kan.cubeCoordinateComplete.eq_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeFaceGenerated.below.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeFaceGenerated.below.casesOn := _root_.SerrePositivity.InfinityCategories.Kan.CubeFaceGenerated.below.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeFaceGenerated.below.comp (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeFaceGenerated.below.comp := _root_.SerrePositivity.InfinityCategories.Kan.CubeFaceGenerated.below.comp

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeFaceGenerated.below.face (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeFaceGenerated.below.face := _root_.SerrePositivity.InfinityCategories.Kan.CubeFaceGenerated.below.face

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeFaceGenerated.below.id (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeFaceGenerated.below.id := _root_.SerrePositivity.InfinityCategories.Kan.CubeFaceGenerated.below.id

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeFaceGenerated.below.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeFaceGenerated.below.rec := _root_.SerrePositivity.InfinityCategories.Kan.CubeFaceGenerated.below.rec
