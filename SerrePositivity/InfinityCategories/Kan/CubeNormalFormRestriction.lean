module
public import SerrePositivity.InfinityCategories.Kan.CubeDeletionGeneration

/-! # 有限 max 表示の入力座標への制限
概要：指定した入力だけに有限 max 表示を制限し、元の使用入力を全て含めば評価を回収する。
方針：各有限集合を選択添字の逆像へ移し、有限 max の真偽を存在量化で比較する。
規約：定数一と空 support を保持する。使われ方：未使用入力を削除した圧縮表示。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 元の有限 max 表示を指定した入力座標へ制限したデータ。 -/
def cubeJoinNormalFormRestrict {n m k : ℕ} (s : CubeJoinNormalForm n m)
    (e : Fin k → Fin n) : CubeJoinNormalForm k m :=
  fun j => (s j).map (fun t => Finset.univ.filter (fun i => e i ∈ t))

/-- 制限した表示の support は、元の support の同じ添字による逆像。 -/
lemma mem_cubeJoinNormalFormRestrict_support {n m k : ℕ} (s : CubeJoinNormalForm n m)
    (e : Fin k → Fin n) (i : Fin k) (j : Fin m) :
    i ∈ cubeJoinNormalFormSupport (cubeJoinNormalFormRestrict s e) j ↔
      e i ∈ cubeJoinNormalFormSupport s j := by
  cases hs : s j <;> simp [cubeJoinNormalFormRestrict, cubeJoinNormalFormSupport, hs]

/-- 元の使用入力を全て含む選択なら、制限した表示の評価は元の評価を回収する。 -/
lemma cubeJoinNormalFormRestrict_eval {n m k : ℕ} (s : CubeJoinNormalForm n m)
    (e : Fin k → Fin n)
    (he : ∀ j i, i ∈ cubeJoinNormalFormSupport s j → i ∈ Set.range e)
    (x : CubeVertex n) :
    cubeJoinNormalFormEval (cubeJoinNormalFormRestrict s e) (cubeCoordinateSelect e x) =
      cubeJoinNormalFormEval s x := by
  funext j
  cases hs : s j with
  | none => simp [cubeJoinNormalFormEval, cubeJoinNormalFormRestrict, hs, cubeJoinTermEval]
  | some t =>
    simp only [cubeJoinNormalFormEval, cubeJoinNormalFormRestrict, hs, Option.map_some,
      cubeJoinTermEval]
    apply Bool.eq_iff_iff.mpr
    change _ = ⊤ ↔ _ = ⊤
    rw [Finset.sup_eq_top_iff, Finset.sup_eq_top_iff]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, cubeCoordinateSelect]
    constructor
    · rintro ⟨i, hi, hx⟩
      exact ⟨e i, hi, hx⟩
    · rintro ⟨i, hi, hx⟩
      have himem : i ∈ cubeJoinNormalFormSupport s j := by
        simpa only [cubeJoinNormalFormSupport, hs, Option.getD_some] using hi
      obtain ⟨a, ha⟩ := he j i himem
      exact ⟨a, ha ▸ hi, ha ▸ hx⟩

end SerrePositivity.KST.SConstruction
