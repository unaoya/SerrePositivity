module
public import SerrePositivity.KST.SConstruction.CubeFacePathIndependence

/-! # max の語の順序つきブロック標準表示
概要：各入力を右端から新しい出力ブロックの開始、または最初のブロックへの結合で表す。
方針：標準表示から入力を出力ブロックへ送る添字写像を回収する。
規約：全入力を使い、全ブロックが空でない。使われ方：max の語の Serre 表示非依存性。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 入力を順序どおりの空でないブロックへまとめる標準表示。 -/
inductive CubeConnectionNormal : ℕ → ℕ → Type
  | nil : CubeConnectionNormal 0 0
  | keep {n m : ℕ} (d : CubeConnectionNormal n m) : CubeConnectionNormal (n + 1) (m + 1)
  | merge {n m : ℕ} (d : CubeConnectionNormal n (m + 1)) :
      CubeConnectionNormal (n + 1) (m + 1)

/-- 標準表示における元の各入力の出力ブロック。 -/
def cubeConnectionNormalBlock : {n m : ℕ} → CubeConnectionNormal n m → (Fin n → Fin m)
  | _, _, .nil => Fin.elim0
  | _, _, .keep d => Fin.cons 0 (fun i => (cubeConnectionNormalBlock d i).succ)
  | _, _, .merge d => Fin.cons 0 (cubeConnectionNormalBlock d)

/-- 最初の元の入力は最初のブロックへ入る。 -/
lemma cubeConnectionNormalBlock_zero {n m : ℕ} (d : CubeConnectionNormal (n + 1) (m + 1)) :
    cubeConnectionNormalBlock d 0 = 0 := by
  cases d <;> rfl

/-- 各入力が別々のブロックである標準表示。 -/
def cubeConnectionNormalId : (n : ℕ) → CubeConnectionNormal n n
  | 0 => .nil
  | n + 1 => .keep (cubeConnectionNormalId n)

/-- 各入力が別々なら、元のブロック添字は恒等。 -/
lemma cubeConnectionNormalId_block (n : ℕ) :
    cubeConnectionNormalBlock (cubeConnectionNormalId n) = _root_.id := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · simp [cubeConnectionNormalId, cubeConnectionNormalBlock, ih]

/-- 元の隣接二出力を結合して、ブロック標準表示へ戻す。 -/
def cubeConnectionNormalConnect : {n m : ℕ} → CubeConnectionNormal n (m + 2) →
    Fin (m + 1) → CubeConnectionNormal n (m + 1)
  | _, 0, .keep d, _ => .merge d
  | _, _ + 1, .keep d, i =>
      Fin.cases (.merge d) (fun j => .keep (cubeConnectionNormalConnect d j)) i
  | _, _, .merge d, i => .merge (cubeConnectionNormalConnect d i)

/-- 元の隣接出力の結合は、同じ隣接二番号を同一視する添字写像の合成。 -/
lemma cubeConnectionNormalConnect_block {n m : ℕ} (d : CubeConnectionNormal n (m + 2))
    (i : Fin (m + 1)) :
    cubeConnectionNormalBlock (cubeConnectionNormalConnect d i) =
      i.predAbove ∘ cubeConnectionNormalBlock d := by
  induction n generalizing m with
  | zero => cases d
  | succ n ih =>
    cases d with
    | keep d =>
      cases m with
      | zero =>
        have hi : i = 0 := Fin.ext (by omega)
        subst i
        funext j
        refine Fin.cases ?_ (fun j => ?_) j
        · simp [cubeConnectionNormalConnect, cubeConnectionNormalBlock]
        · simp [cubeConnectionNormalConnect, cubeConnectionNormalBlock]
      | succ m =>
        refine Fin.cases ?_ (fun i => ?_) i
        · funext j
          refine Fin.cases ?_ (fun j => ?_) j
          · simp [cubeConnectionNormalConnect, cubeConnectionNormalBlock]
          · simp [cubeConnectionNormalConnect, cubeConnectionNormalBlock]
        · funext j
          refine Fin.cases ?_ (fun j => ?_) j
          · simp [cubeConnectionNormalConnect, cubeConnectionNormalBlock]
          · simpa [cubeConnectionNormalConnect, cubeConnectionNormalBlock] using
              congrArg Fin.succ (congrFun (ih d i) j)
    | merge d =>
      funext j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp [cubeConnectionNormalConnect, cubeConnectionNormalBlock]
      · simpa [cubeConnectionNormalConnect, cubeConnectionNormalBlock] using
          congrFun (ih d i) j

end SerrePositivity.KST.SConstruction
