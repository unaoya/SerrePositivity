module
public import SerrePositivity.KST.SConstruction.SimplexHAOrderAppendLast

/-! # 元の内部切断の左右の昇順頂点列
概要：指定した内部頂点で、元の列を切断前の列と切断頂点から始まる列へ分ける。
方針：元の数値頂点番号を左右のブロックへ制限する。
規約：共有頂点・最右頂点と元の順序を保持。使われ方：内部一端点の HA 値分解。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 元の内部切断より左の列。切断頂点は右端として別に保持する。 -/
def simplexHASplitLeft {N : ℕ} (n m : ℕ) (v : Fin (n + 1 + m + 1) ↪o Fin (N + 1)) :
    Fin (n + 1) ↪o Fin (N + 1) :=
  OrderEmbedding.ofStrictMono (fun j => v ⟨j.val, by omega⟩)
    (fun _ _ h => v.strictMono (by exact h))

/-- 元の内部切断から右の列。切断頂点を始点として保持する。 -/
def simplexHASplitRight {N : ℕ} (n m : ℕ) (v : Fin (n + 1 + m + 1) ↪o Fin (N + 1)) :
    Fin (m + 1) ↪o Fin (N + 1) :=
  OrderEmbedding.ofStrictMono (fun j => v ⟨n + 1 + j.val, by omega⟩)
    (fun i j h => v.strictMono (by
      change n + 1 + i.val < n + 1 + j.val
      exact Nat.add_lt_add_left h (n + 1)))

/-- 元の左右ブロックが共有する、元の内部切断頂点。 -/
def simplexHASplitCut {N : ℕ} (n m : ℕ) (v : Fin (n + 1 + m + 1) ↪o Fin (N + 1)) :
    Fin (N + 1) := v ⟨n + 1, by omega⟩

/-- 元の左ブロックは、元の同じ始点を保つ。 -/
lemma simplexHASplitLeft_first {N : ℕ} (n m : ℕ)
    (v : Fin (n + 1 + m + 1) ↪o Fin (N + 1)) : simplexHASplitLeft n m v 0 = v 0 := rfl

/-- 元の左ブロックの最後は、元の切断頂点より厳密に左。 -/
lemma simplexHASplitLeft_last_lt {N : ℕ} (n m : ℕ)
    (v : Fin (n + 1 + m + 1) ↪o Fin (N + 1)) :
    simplexHASplitLeft n m v (Fin.last n) < simplexHASplitCut n m v :=
  v.strictMono (by change n < n + 1; omega)

/-- 元の右ブロックは、元の同じ切断頂点を始点とする。 -/
lemma simplexHASplitRight_first {N : ℕ} (n m : ℕ)
    (v : Fin (n + 1 + m + 1) ↪o Fin (N + 1)) :
    simplexHASplitRight n m v 0 = simplexHASplitCut n m v := by
  exact congrArg v (Fin.ext (by simp only [Fin.val_zero, Nat.add_zero]))

/-- 元の右ブロックは、元の同じ最右頂点を保つ。 -/
lemma simplexHASplitRight_last {N : ℕ} (n m : ℕ)
    (v : Fin (n + 1 + m + 1) ↪o Fin (N + 1)) :
    simplexHASplitRight n m v (Fin.last m) = v (Fin.last (n + 1 + m)) := rfl

/-- 元の最右頂点を除く制限は、元の左ブロックを変えない。 -/
lemma simplexHASplitLeft_prefix {N : ℕ} (n m : ℕ)
    (v : Fin (n + 1 + (m + 1) + 1) ↪o Fin (N + 1)) :
    simplexHASplitLeft n (m + 1) v =
      simplexHASplitLeft n m (Fin.castSuccOrderEmb.trans v) := rfl

/-- 元の最右頂点を除く制限は、元の同じ切断頂点を保つ。 -/
lemma simplexHASplitCut_prefix {N : ℕ} (n m : ℕ)
    (v : Fin (n + 1 + (m + 1) + 1) ↪o Fin (N + 1)) :
    simplexHASplitCut n (m + 1) v =
      simplexHASplitCut n m (Fin.castSuccOrderEmb.trans v) := rfl

/-- 元の右ブロックの前段は、元の全列の前段の同じ右ブロック。 -/
lemma simplexHASplitRight_prefix {N : ℕ} (n m : ℕ)
    (v : Fin (n + 1 + (m + 1) + 1) ↪o Fin (N + 1)) :
    Fin.castSuccOrderEmb.trans (simplexHASplitRight n (m + 1) v) =
      simplexHASplitRight n m (Fin.castSuccOrderEmb.trans v) := rfl

/-- 元の零右次元では、左ブロックは元の前段列そのもの。 -/
lemma simplexHASplitLeft_zero {N : ℕ} (n : ℕ)
    (v : Fin (n + 1 + 0 + 1) ↪o Fin (N + 1)) :
    simplexHASplitLeft n 0 v = Fin.castSuccOrderEmb.trans v := rfl

/-- 元の零右次元では、切断頂点は元の最右頂点そのもの。 -/
lemma simplexHASplitCut_zero {N : ℕ} (n : ℕ)
    (v : Fin (n + 1 + 0 + 1) ↪o Fin (N + 1)) :
    simplexHASplitCut n 0 v = v (Fin.last (n + 1)) := rfl

end SerrePositivity.KST.SConstruction
