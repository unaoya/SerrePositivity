module
public import SerrePositivity.KST.SConstruction.CubeThreeNormalResults

/-! # 三段表示の各因子の端点と頂点での検出
概要：削除と非空ブロック max は両端点を保ち、面の保持入力は端点から検出できる。
方針：各標準表示を帰納し、全入力と全出力の元の座標を保持する。
規約：中間次元を固定する仮定は置かない。使われ方：三段表示の意味による一意性。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 全ての元の max ブロックは空でない。 -/
lemma cubeConnectionNormalBlock_surjective {n m : ℕ} (d : CubeConnectionNormal n m) :
    Function.Surjective (cubeConnectionNormalBlock d) := by
  induction d with
  | nil => intro j; exact Fin.elim0 j
  | keep d ih =>
    intro j
    refine Fin.cases ⟨0, rfl⟩ (fun j => ?_) j
    obtain ⟨i, hi⟩ := ih j
    exact ⟨i.succ, congrArg Fin.succ hi⟩
  | merge d ih =>
    intro j
    obtain ⟨i, hi⟩ := ih j
    exact ⟨i.succ, hi⟩

/-- 元の max 評価は零頂点を保つ。 -/
lemma cubeConnectionNormalVertex_bot {n m : ℕ} (d : CubeConnectionNormal n m) :
    cubeConnectionNormalVertex d ⊥ = ⊥ := by
  funext j
  apply Bool.eq_iff_iff.mpr
  simp [cubeConnectionNormalVertex, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax_true_iff]

/-- 空でない元の各ブロックの max は一頂点を保つ。 -/
lemma cubeConnectionNormalVertex_top {n m : ℕ} (d : CubeConnectionNormal n m) :
    cubeConnectionNormalVertex d ⊤ = ⊤ := by
  funext j
  obtain ⟨i, hi⟩ := cubeConnectionNormalBlock_surjective d j
  exact (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax_true_iff _ _ _).mpr ⟨i, hi, rfl⟩

/-- 元の削除評価は零頂点を保つ。 -/
lemma cubeDeletionNormalVertex_bot {n m : ℕ} (d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionNormal n m) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex d ⊥ = ⊥ := rfl

/-- 元の削除評価は一頂点を保つ。 -/
lemma cubeDeletionNormalVertex_top {n m : ℕ} (d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionNormal n m) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex d ⊤ = ⊤ := rfl

/-- 元の削除評価は全ての残余頂点を回収する。 -/
lemma cubeDeletionNormalVertex_surjective {n m : ℕ} (d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionNormal n m) :
    Function.Surjective (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex d) := by
  induction d with
  | nil => intro y; exact ⟨y, Subsingleton.elim _ _⟩
  | drop d ih =>
    intro y
    obtain ⟨x, hx⟩ := ih y
    exact ⟨Fin.cons false x, hx⟩
  | keep d ih =>
    intro y
    obtain ⟨x, hx⟩ := ih (fun j => y j.succ)
    refine ⟨Fin.cons (y 0) x, ?_⟩
    funext j
    refine Fin.cases rfl (fun j => ?_) j
    exact congrFun hx j

/-- 元の面の頂点写像は保持する全入力を検出する。 -/
lemma cubeFaceNormalVertex_injective_input {n m : ℕ} (d : CubeFaceNormal n m) :
    Function.Injective (cubeFaceNormalVertex d) := by
  induction d with
  | nil => intro x y h; exact h
  | point b d ih =>
    intro x y h
    apply ih
    funext j
    exact congrFun h j.succ
  | keep d ih =>
    intro x y h
    have htail : Fin.tail x = Fin.tail y := by
      apply ih
      funext j
      exact congrFun h j.succ
    funext j
    refine Fin.cases (congrFun h 0) (fun j => congrFun htail j) j

/-- 面の両端点は、保持する入力の次元も検出する。 -/
lemma cubeFaceNormal_dimension_of_endpoints {a b m : ℕ}
    (d : CubeFaceNormal a m) (e : CubeFaceNormal b m)
    (hzero : cubeFaceNormalVertex d ⊥ = cubeFaceNormalVertex e ⊥)
    (hone : cubeFaceNormalVertex d ⊤ = cubeFaceNormalVertex e ⊤) : a = b := by
  induction d generalizing b with
  | nil => cases e; rfl
  | point c d ih =>
    cases e with
    | point c' e =>
      apply ih e
      · funext j; exact congrFun hzero j.succ
      · funext j; exact congrFun hone j.succ
    | keep e =>
      have hz := congrFun hzero 0
      have ho := congrFun hone 0
      cases c <;> simp [cubeFaceNormalVertex] at hz ho
  | keep d ih =>
    cases e with
    | point c e =>
      have hz := congrFun hzero 0
      have ho := congrFun hone 0
      cases c <;> simp [cubeFaceNormalVertex] at hz ho
    | keep e =>
      congr 1
      apply ih e
      · funext j; exact congrFun hzero j.succ
      · funext j; exact congrFun hone j.succ

/-- 同じ入力次元の面は、両端点だけから一意に回収される。 -/
lemma cubeFaceNormal_eq_of_endpoints {n m : ℕ} (d e : CubeFaceNormal n m)
    (hzero : cubeFaceNormalVertex d ⊥ = cubeFaceNormalVertex e ⊥)
    (hone : cubeFaceNormalVertex d ⊤ = cubeFaceNormalVertex e ⊤) : d = e := by
  induction d with
  | nil => cases e; rfl
  | point c d ih =>
    cases e with
    | point c' e =>
      have hc : c = c' := congrFun hzero 0
      have hd : d = e := ih e (funext fun j => congrFun hzero j.succ)
        (funext fun j => congrFun hone j.succ)
      cases hc
      cases hd
      rfl
    | keep e =>
      have hz := congrFun hzero 0
      have ho := congrFun hone 0
      cases c <;> simp [cubeFaceNormalVertex] at hz ho
  | keep d ih =>
    cases e with
    | point c e =>
      have hz := congrFun hzero 0
      have ho := congrFun hone 0
      cases c <;> simp [cubeFaceNormalVertex] at hz ho
    | keep e =>
      congr 1
      exact ih e (funext fun j => congrFun hzero j.succ)
        (funext fun j => congrFun hone j.succ)

end SerrePositivity.KST.SConstruction
