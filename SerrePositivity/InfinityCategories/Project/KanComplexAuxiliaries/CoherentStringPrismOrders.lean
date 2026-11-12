module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentStringEndpoints

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
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped _root_.Simplicial

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
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringExtend θ).toOrderHom i.castSucc = (θ.toOrderHom i).castSucc := by
  simp [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringExtend]

/-- 下側への延長は新しい終点を保持する。 -/
lemma coherentLowerStringExtend_last {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringExtend θ).toOrderHom (Fin.last (m + 1)) = Fin.last (n + 1) := by
  simp [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringExtend]

/-- 上側への延長は新しい始点を保持する。 -/
lemma coherentUpperStringExtend_zero {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringExtend θ).toOrderHom 0 = 0 := by
  simp [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringExtend]

/-- 上側への延長は元の各入力頂点を厳密に保つ。 -/
lemma coherentUpperStringExtend_succ {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringExtend θ).toOrderHom i.succ = (θ.toOrderHom i).succ := by
  simp [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringExtend]

/-- 終点を保つ再添字では、下側の入力列への射影も厳密に可換。 -/
lemma coherentLowerStringExtend_index {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (hθ : θ.toOrderHom (Fin.last m) = Fin.last n) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringExtend θ ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringIndex n =
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringIndex m ≫ θ := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  cases i using Fin.lastCases <;>
    simp [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringExtend, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringIndex, hθ]

/-- 始点を保つ再添字では、上側の入力列への射影も厳密に可換。 -/
lemma coherentUpperStringExtend_index {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (hθ : θ.toOrderHom 0 = 0) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringExtend θ ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringIndex n =
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringIndex m ≫ θ := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  cases i using Fin.cases <;>
    simp [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringExtend, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringIndex, hθ]

/-- 下側への延長は元の時刻を全頂点で保つ。 -/
lemma coherentLowerStringExtend_time {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringExtend θ ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringTime n = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringTime m := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  cases i using Fin.lastCases <;> simp [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringExtend, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringTime]

/-- 上側への延長も元の時刻を全頂点で保つ。 -/
lemma coherentUpperStringExtend_time {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringExtend θ ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringTime n = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringTime m := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  cases i using Fin.cases <;> simp [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringExtend, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringTime]


/-- 下側の入力への射影は元の始点を厳密に保つ。 -/
lemma coherentLowerStringIndex_first (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringIndex n).toOrderHom 0 = 0 := by
  change Fin.lastCases (motive := fun _ => Fin (n + 1)) (Fin.last n)
    (fun i : Fin (n + 1) => i) (0 : Fin (n + 1)).castSucc = _
  rw [Fin.lastCases_castSucc]

/-- 下側の入力への射影は元の終点を厳密に保つ。 -/
lemma coherentLowerStringIndex_last (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringIndex n).toOrderHom (Fin.last (n + 1)) = Fin.last n := by
  simp [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringIndex]

/-- 下側の時刻は元の始点を厳密に保つ。 -/
lemma coherentLowerStringTime_first (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringTime n).toOrderHom 0 = 0 := by
  change Fin.lastCases (motive := fun _ => Fin 2) 1
    (fun _ : Fin (n + 1) => (0 : Fin 2)) (0 : Fin (n + 1)).castSucc = _
  rw [Fin.lastCases_castSucc]

/-- 下側の時刻は元の終点を厳密に保つ。 -/
lemma coherentLowerStringTime_last (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringTime n).toOrderHom (Fin.last (n + 1)) = 1 := by
  simp [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringTime]

/-- 下側への延長は恒等再添字を厳密に保つ。 -/
lemma coherentLowerStringExtend_id (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringExtend (𝟙 ⦋n⦌) = 𝟙 ⦋n + 1⦌ := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  cases i using Fin.lastCases <;> simp [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringExtend]

/-- 下側への延長は再添字の合成を厳密に保つ。 -/
lemma coherentLowerStringExtend_comp {l m n : ℕ} (θ : ⦋l⦌ ⟶ ⦋m⦌) (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringExtend (θ ≫ φ) =
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringExtend θ ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringExtend φ := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  cases i using Fin.lastCases <;> simp [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringExtend]

/-- 上側の入力への射影は元の始点を厳密に保つ。 -/
lemma coherentUpperStringIndex_first (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringIndex n).toOrderHom 0 = 0 := by
  simp [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringIndex]

/-- 上側の入力への射影は元の終点を厳密に保つ。 -/
lemma coherentUpperStringIndex_last (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringIndex n).toOrderHom (Fin.last (n + 1)) = Fin.last n := by
  change Fin.cases (motive := fun _ => Fin (n + 1)) 0
    (fun i : Fin (n + 1) => i) (Fin.last n).succ = _
  rw [Fin.cases_succ]

/-- 上側の時刻は元の始点を厳密に保つ。 -/
lemma coherentUpperStringTime_first (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringTime n).toOrderHom 0 = 0 := by
  simp [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringTime]

/-- 上側の時刻は元の終点を厳密に保つ。 -/
lemma coherentUpperStringTime_last (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringTime n).toOrderHom (Fin.last (n + 1)) = 1 := by
  change Fin.cases (motive := fun _ => Fin 2) 0
    (fun _ : Fin (n + 1) => (1 : Fin 2)) (Fin.last n).succ = _
  rw [Fin.cases_succ]

/-- 上側への延長は恒等再添字を厳密に保つ。 -/
lemma coherentUpperStringExtend_id (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringExtend (𝟙 ⦋n⦌) = 𝟙 ⦋n + 1⦌ := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  cases i using Fin.cases <;> simp [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringExtend]

/-- 上側への延長は再添字の合成を厳密に保つ。 -/
lemma coherentUpperStringExtend_comp {l m n : ℕ} (θ : ⦋l⦌ ⟶ ⦋m⦌) (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringExtend (θ ≫ φ) =
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringExtend θ ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringExtend φ := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  cases i using Fin.cases <;> simp [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringExtend]

/-- 下側への延長は元の始点固定を保持する。 -/
lemma coherentLowerStringExtend_first {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (hθ : θ.toOrderHom 0 = 0) :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringExtend θ).toOrderHom 0 = 0 := by
  change (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringExtend θ).toOrderHom (0 : Fin (m + 1)).castSucc = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringExtend_castSucc, hθ]
  rfl

/-- 上側への延長は元の終点固定を保持する。 -/
lemma coherentUpperStringExtend_last {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (hθ : θ.toOrderHom (Fin.last m) = Fin.last n) :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringExtend θ).toOrderHom (Fin.last (m + 1)) = Fin.last (n + 1) := by
  change (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringExtend θ).toOrderHom (Fin.last m).succ = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringExtend_succ, hθ]
  rfl

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringExtend (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentLowerStringExtend := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringExtend

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentLowerStringExtend_castSucc := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringExtend_castSucc

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentLowerStringExtend_comp := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringExtend_comp

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentLowerStringExtend_first := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringExtend_first

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentLowerStringExtend_id := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringExtend_id

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentLowerStringExtend_index := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringExtend_index

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentLowerStringExtend_last := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringExtend_last

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentLowerStringExtend_time := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringExtend_time

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringIndex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentLowerStringIndex := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringIndex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentLowerStringIndex_first := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringIndex_first

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentLowerStringIndex_last := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringIndex_last

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringTime (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentLowerStringTime := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringTime

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentLowerStringTime_first := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringTime_first

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentLowerStringTime_last := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringTime_last

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringExtend (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentUpperStringExtend := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringExtend

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentUpperStringExtend_comp := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringExtend_comp

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentUpperStringExtend_id := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringExtend_id

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentUpperStringExtend_index := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringExtend_index

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentUpperStringExtend_last := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringExtend_last

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentUpperStringExtend_succ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringExtend_succ

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentUpperStringExtend_time := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringExtend_time

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentUpperStringExtend_zero := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringExtend_zero

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringIndex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentUpperStringIndex := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringIndex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentUpperStringIndex_first := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringIndex_first

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentUpperStringIndex_last := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringIndex_last

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringTime (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentUpperStringTime := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringTime

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentUpperStringTime_first := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringTime_first

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentUpperStringTime_last := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringTime_last

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentLowerStringExtend._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringExtend._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentLowerStringExtend.eq_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringExtend.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentLowerStringIndex._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringIndex._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentLowerStringIndex.eq_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringIndex.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentLowerStringTime._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringTime._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentLowerStringTime._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringTime._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentLowerStringTime.eq_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringTime.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentUpperStringExtend._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringExtend._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentUpperStringExtend._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringExtend._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentUpperStringExtend.eq_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringExtend.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentUpperStringIndex._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringIndex._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentUpperStringIndex._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringIndex._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentUpperStringIndex.eq_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringIndex.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentUpperStringTime._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringTime._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.coherentUpperStringTime.eq_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringTime.eq_1
