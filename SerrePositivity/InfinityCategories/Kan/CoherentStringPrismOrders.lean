module
public import SerrePositivity.InfinityCategories.Kan.CoherentStringEndpoints

/-! # 上下の因子分解列の端点再添字
概要：元の合成列に始点又は終点の縦辺を付ける単体作用を構成する。
方針：最初又は最後に一点を加え、元の再添字と時刻を厳密に保持する。
規約：長さ零の合成列と退化する再添字も含む。
使われ方：同じ元の合成列を prism の下側・上側の二つの因子分解列へ送る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial

/-- 終点を一回繰り返す元の入力列への射影。 -/
def coherentLowerStringIndex (n : ℕ) : ⦋n + 1⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.mkHom ⟨Fin.lastCases (Fin.last n) (fun i => i), by
    intro i j hij
    cases i using Fin.lastCases <;> cases j using Fin.lastCases <;>
      simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
    · exact le_rfl
    · simp only [Fin.le_def, Fin.val_last, Fin.val_castSucc] at hij
      omega
    · exact Fin.le_last _
    · exact Fin.castSucc_le_castSucc_iff.mp hij⟩

/-- 始点を一回繰り返す元の入力列への射影。 -/
def coherentUpperStringIndex (n : ℕ) : ⦋n + 1⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.mkHom ⟨Fin.cases 0 (fun i => i), by
    intro i j hij
    cases i using Fin.cases <;> cases j using Fin.cases <;>
      simp only [Fin.cases_zero, Fin.cases_succ]
    · exact le_rfl
    · exact Fin.zero_le _
    · simp only [Fin.le_def, Fin.val_succ, Fin.val_zero] at hij
      omega
    · exact Fin.succ_le_succ_iff.mp hij⟩

/-- 下側の列では、最後の一頂点だけが上段の時刻。 -/
def coherentLowerStringTime (n : ℕ) : ⦋n + 1⦌ ⟶ ⦋1⦌ :=
  SimplexCategory.mkHom ⟨Fin.lastCases 1 (fun _ => 0), by
    intro i j hij
    cases i using Fin.lastCases <;> cases j using Fin.lastCases <;>
      simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
    · exact le_rfl
    · simp only [Fin.le_def, Fin.val_last, Fin.val_castSucc] at hij
      omega
    · exact Fin.zero_le _
    · exact le_rfl⟩

/-- 上側の列では、最初の一頂点だけが下段の時刻。 -/
def coherentUpperStringTime (n : ℕ) : ⦋n + 1⦌ ⟶ ⦋1⦌ :=
  SimplexCategory.mkHom ⟨Fin.cases 0 (fun _ => 1), by
    intro i j hij
    cases i using Fin.cases <;> cases j using Fin.cases <;>
      simp only [Fin.cases_zero, Fin.cases_succ]
    · exact le_rfl
    · exact Fin.zero_le _
    · simp only [Fin.le_def, Fin.val_succ, Fin.val_zero] at hij
      omega
    · exact le_rfl⟩

/-- 元の再添字を、終点に一点を加えた合成列へ延長する。 -/
def coherentLowerStringExtend {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) : ⦋m + 1⦌ ⟶ ⦋n + 1⦌ :=
  SimplexCategory.mkHom ⟨Fin.lastCases (Fin.last (n + 1)) (fun i => (θ.toOrderHom i).castSucc), by
    intro i j hij
    cases i using Fin.lastCases <;> cases j using Fin.lastCases <;>
      simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
    · exact le_rfl
    · simp only [Fin.le_def, Fin.val_last, Fin.val_castSucc] at hij
      omega
    · exact Fin.le_last _
    · exact Fin.castSucc_le_castSucc_iff.mpr
        (θ.toOrderHom.monotone (Fin.castSucc_le_castSucc_iff.mp hij))⟩

/-- 元の再添字を、始点に一点を加えた合成列へ延長する。 -/
def coherentUpperStringExtend {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) : ⦋m + 1⦌ ⟶ ⦋n + 1⦌ :=
  SimplexCategory.mkHom ⟨Fin.cases 0 (fun i => (θ.toOrderHom i).succ), by
    intro i j hij
    cases i using Fin.cases <;> cases j using Fin.cases <;>
      simp only [Fin.cases_zero, Fin.cases_succ]
    · exact le_rfl
    · exact Fin.zero_le _
    · simp only [Fin.le_def, Fin.val_succ, Fin.val_zero] at hij
      omega
    · exact Fin.succ_le_succ_iff.mpr
        (θ.toOrderHom.monotone (Fin.succ_le_succ_iff.mp hij))⟩

/-- 下側への延長は元の各入力頂点を厳密に保つ。 -/
lemma coherentLowerStringExtend_castSucc {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 1)) :
    (coherentLowerStringExtend θ).toOrderHom i.castSucc = (θ.toOrderHom i).castSucc := by
  simp [coherentLowerStringExtend]

/-- 下側への延長は新しい終点を保持する。 -/
lemma coherentLowerStringExtend_last {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (coherentLowerStringExtend θ).toOrderHom (Fin.last (m + 1)) = Fin.last (n + 1) := by
  simp [coherentLowerStringExtend]

/-- 上側への延長は新しい始点を保持する。 -/
lemma coherentUpperStringExtend_zero {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (coherentUpperStringExtend θ).toOrderHom 0 = 0 := by
  simp [coherentUpperStringExtend]

/-- 上側への延長は元の各入力頂点を厳密に保つ。 -/
lemma coherentUpperStringExtend_succ {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 1)) :
    (coherentUpperStringExtend θ).toOrderHom i.succ = (θ.toOrderHom i).succ := by
  simp [coherentUpperStringExtend]

/-- 終点を保つ再添字では、下側の入力列への射影も厳密に可換。 -/
lemma coherentLowerStringExtend_index {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (hθ : θ.toOrderHom (Fin.last m) = Fin.last n) :
    coherentLowerStringExtend θ ≫ coherentLowerStringIndex n =
      coherentLowerStringIndex m ≫ θ := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  cases i using Fin.lastCases <;>
    simp [coherentLowerStringExtend, coherentLowerStringIndex, hθ]

/-- 始点を保つ再添字では、上側の入力列への射影も厳密に可換。 -/
lemma coherentUpperStringExtend_index {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (hθ : θ.toOrderHom 0 = 0) :
    coherentUpperStringExtend θ ≫ coherentUpperStringIndex n =
      coherentUpperStringIndex m ≫ θ := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  cases i using Fin.cases <;>
    simp [coherentUpperStringExtend, coherentUpperStringIndex, hθ]

/-- 下側への延長は元の時刻を全頂点で保つ。 -/
lemma coherentLowerStringExtend_time {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    coherentLowerStringExtend θ ≫ coherentLowerStringTime n = coherentLowerStringTime m := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  cases i using Fin.lastCases <;> simp [coherentLowerStringExtend, coherentLowerStringTime]

/-- 上側への延長も元の時刻を全頂点で保つ。 -/
lemma coherentUpperStringExtend_time {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    coherentUpperStringExtend θ ≫ coherentUpperStringTime n = coherentUpperStringTime m := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  cases i using Fin.cases <;> simp [coherentUpperStringExtend, coherentUpperStringTime]


/-- 下側の入力への射影は元の始点を厳密に保つ。 -/
lemma coherentLowerStringIndex_first (n : ℕ) :
    (coherentLowerStringIndex n).toOrderHom 0 = 0 := by
  change Fin.lastCases (motive := fun _ => Fin (n + 1)) (Fin.last n)
    (fun i : Fin (n + 1) => i) (0 : Fin (n + 1)).castSucc = _
  rw [Fin.lastCases_castSucc]

/-- 下側の入力への射影は元の終点を厳密に保つ。 -/
lemma coherentLowerStringIndex_last (n : ℕ) :
    (coherentLowerStringIndex n).toOrderHom (Fin.last (n + 1)) = Fin.last n := by
  simp [coherentLowerStringIndex]

/-- 下側の時刻は元の始点を厳密に保つ。 -/
lemma coherentLowerStringTime_first (n : ℕ) :
    (coherentLowerStringTime n).toOrderHom 0 = 0 := by
  change Fin.lastCases (motive := fun _ => Fin 2) 1
    (fun _ : Fin (n + 1) => (0 : Fin 2)) (0 : Fin (n + 1)).castSucc = _
  rw [Fin.lastCases_castSucc]

/-- 下側の時刻は元の終点を厳密に保つ。 -/
lemma coherentLowerStringTime_last (n : ℕ) :
    (coherentLowerStringTime n).toOrderHom (Fin.last (n + 1)) = 1 := by
  simp [coherentLowerStringTime]

/-- 下側への延長は恒等再添字を厳密に保つ。 -/
lemma coherentLowerStringExtend_id (n : ℕ) :
    coherentLowerStringExtend (𝟙 ⦋n⦌) = 𝟙 ⦋n + 1⦌ := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  cases i using Fin.lastCases <;> simp [coherentLowerStringExtend]

/-- 下側への延長は再添字の合成を厳密に保つ。 -/
lemma coherentLowerStringExtend_comp {l m n : ℕ} (θ : ⦋l⦌ ⟶ ⦋m⦌) (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    coherentLowerStringExtend (θ ≫ φ) =
      coherentLowerStringExtend θ ≫ coherentLowerStringExtend φ := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  cases i using Fin.lastCases <;> simp [coherentLowerStringExtend]

/-- 上側の入力への射影は元の始点を厳密に保つ。 -/
lemma coherentUpperStringIndex_first (n : ℕ) :
    (coherentUpperStringIndex n).toOrderHom 0 = 0 := by
  simp [coherentUpperStringIndex]

/-- 上側の入力への射影は元の終点を厳密に保つ。 -/
lemma coherentUpperStringIndex_last (n : ℕ) :
    (coherentUpperStringIndex n).toOrderHom (Fin.last (n + 1)) = Fin.last n := by
  change Fin.cases (motive := fun _ => Fin (n + 1)) 0
    (fun i : Fin (n + 1) => i) (Fin.last n).succ = _
  rw [Fin.cases_succ]

/-- 上側の時刻は元の始点を厳密に保つ。 -/
lemma coherentUpperStringTime_first (n : ℕ) :
    (coherentUpperStringTime n).toOrderHom 0 = 0 := by
  simp [coherentUpperStringTime]

/-- 上側の時刻は元の終点を厳密に保つ。 -/
lemma coherentUpperStringTime_last (n : ℕ) :
    (coherentUpperStringTime n).toOrderHom (Fin.last (n + 1)) = 1 := by
  change Fin.cases (motive := fun _ => Fin 2) 0
    (fun _ : Fin (n + 1) => (1 : Fin 2)) (Fin.last n).succ = _
  rw [Fin.cases_succ]

/-- 上側への延長は恒等再添字を厳密に保つ。 -/
lemma coherentUpperStringExtend_id (n : ℕ) :
    coherentUpperStringExtend (𝟙 ⦋n⦌) = 𝟙 ⦋n + 1⦌ := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  cases i using Fin.cases <;> simp [coherentUpperStringExtend]

/-- 上側への延長は再添字の合成を厳密に保つ。 -/
lemma coherentUpperStringExtend_comp {l m n : ℕ} (θ : ⦋l⦌ ⟶ ⦋m⦌) (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    coherentUpperStringExtend (θ ≫ φ) =
      coherentUpperStringExtend θ ≫ coherentUpperStringExtend φ := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  cases i using Fin.cases <;> simp [coherentUpperStringExtend]

/-- 下側への延長は元の始点固定を保持する。 -/
lemma coherentLowerStringExtend_first {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (hθ : θ.toOrderHom 0 = 0) :
    (coherentLowerStringExtend θ).toOrderHom 0 = 0 := by
  change (coherentLowerStringExtend θ).toOrderHom (0 : Fin (m + 1)).castSucc = _
  rw [coherentLowerStringExtend_castSucc, hθ]
  rfl

/-- 上側への延長は元の終点固定を保持する。 -/
lemma coherentUpperStringExtend_last {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (hθ : θ.toOrderHom (Fin.last m) = Fin.last n) :
    (coherentUpperStringExtend θ).toOrderHom (Fin.last (m + 1)) = Fin.last (n + 1) := by
  change (coherentUpperStringExtend θ).toOrderHom (Fin.last m).succ = _
  rw [coherentUpperStringExtend_succ, hθ]
  rfl

end SerrePositivity.KST.SConstruction
