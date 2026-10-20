module
public import SerrePositivity.KST.SConstruction.CubeNormalFormRestriction

/-! # 選択した入力を元の座標へ戻す零面挿入
概要：順序を保つ座標選択に対し、他の座標を零で埋める実際の逆向き射を作る。
方針：各座標の有限 max で定義し、未使用座標の零面挿入による次元帰納を使う。
規約：選択との合成は恒等。使われ方：圧縮した表示も元の具体的 cubical 射として実現する。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 指定された入力座標だけを戻し、他の座標を零で埋める元の頂点関数。 -/
def cubeCoordinateInsert {n m : ℕ} (e : Fin m → Fin n) : CubeVertex m → CubeVertex n :=
  fun x i => (Finset.univ.filter (fun j => e j = i)).sup x

/-- 零埋め挿入の真の値は、元の選択の同じ添字で検出される。 -/
lemma cubeCoordinateInsert_true_iff {n m : ℕ} (e : Fin m → Fin n)
    (x : CubeVertex m) (i : Fin n) :
    cubeCoordinateInsert e x i = true ↔ ∃ j, e j = i ∧ x j = true := by
  change (Finset.univ.filter (fun j => e j = i)).sup x = ⊤ ↔ _
  rw [Finset.sup_eq_top_iff]
  simp

/-- 入力を戻してから同じ座標を選ぶと、元の全頂点を厳密に回収する。 -/
lemma cubeCoordinateSelect_insert {n m : ℕ} (e : Fin m → Fin n)
    (he : Function.Injective e) (x : CubeVertex m) :
    cubeCoordinateSelect e (cubeCoordinateInsert e x) = x := by
  funext j
  apply Bool.eq_iff_iff.mpr
  change cubeCoordinateInsert e x (e j) = true ↔ x j = true
  rw [cubeCoordinateInsert_true_iff]
  constructor
  · rintro ⟨i, hi, hx⟩
    exact he hi ▸ hx
  · intro hx
    exact ⟨j, rfl, hx⟩

/-- 元の零埋め挿入は、低次元の挿入と元の未使用座標への零面の合成。 -/
lemma cubeCoordinateInsert_lower {n m : ℕ} (e : Fin m → Fin (n + 1))
    (p : Fin (n + 1)) (hp : ∀ j, e j ≠ p) :
    cubeCoordinateInsert e = cubeVertexFace false n p ∘
      cubeCoordinateInsert (cubeCoordinateLower e p hp) := by
  funext x k
  refine Fin.succAboveCases p ?_ (fun k => ?_) k
  · apply Bool.eq_iff_iff.mpr
    change cubeCoordinateInsert e x p = true ↔ cubeVertexFace false n p _ p = true
    rw [cubeCoordinateInsert_true_iff]
    simp [cubeVertexFace, hp]
  · apply Bool.eq_iff_iff.mpr
    change cubeCoordinateInsert e x (p.succAbove k) = true ↔
      cubeVertexFace false n p _ (p.succAbove k) = true
    simp only [cubeVertexFace, Fin.insertNth_apply_succAbove, cubeCoordinateInsert_true_iff]
    apply exists_congr
    intro j
    rw [← cubeCoordinateLower_spec e p hp j,
      (Fin.strictMono_succAbove p).injective.eq_iff]

/-- 順序を保つ選択に対する零埋め挿入は、元の零面の合成として生成される。 -/
lemma cubeCoordinateInsert_generated {n m : ℕ} (e : Fin m → Fin n) (he : StrictMono e) :
    CubeMapGenerated (cubeCoordinateInsert e) := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero =>
      have h : cubeCoordinateInsert e = (_root_.id : CubeVertex 0 → CubeVertex 0) := by
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
      have hid : cubeCoordinateInsert e = (_root_.id : CubeVertex (n + 1) → _) := by
        funext x j
        apply Bool.eq_iff_iff.mpr
        rw [cubeCoordinateInsert_true_iff, he.eq_id]
        simp
      rw [hid]
      exact .id (n + 1)
    · simp only [Function.Surjective, not_forall, not_exists] at hs
      obtain ⟨p, hp⟩ := hs
      rw [cubeCoordinateInsert_lower e p hp]
      exact .comp (ih _ (cubeCoordinateLower_strictMono e p hp he)) (.face false n p)

end SerrePositivity.KST.SConstruction
