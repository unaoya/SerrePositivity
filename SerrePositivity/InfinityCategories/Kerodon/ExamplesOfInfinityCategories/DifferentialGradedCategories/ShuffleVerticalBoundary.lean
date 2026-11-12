module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleHorizontalBoundary
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleTranspose

/-!
# shuffle の垂直境界添字の同値

概要：第二因子の面番号と大きい shuffle の純粋垂直境界を同値にする。
方針：水平集合の補集合による二因子交換を、証明済みの水平境界の同値と合成する。
規約：KST Construction A.5、全次数 p+q=n。
使われ方：垂直境界和と第二因子の通常境界和の並べ替え。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

/-- 概要：補集合による shuffle の二因子交換の実同値。
方針：補集合を二回取ることを両逆とする。
規約：KST A.5。使われ方：第二因子の面番号の水平の順位への移送。 -/
def shuffleTransposeEquiv (p q n : ℕ) (h : p + q = n) : ShuffleIndex p n ≃ ShuffleIndex q n where
  toFun s := s.transpose h
  invFun s := s.transpose (show q + p = n by omega)
  left_inv s := s.transpose_transpose h
  right_inv s := s.transpose_transpose (show q + p = n by omega)

/-- 概要：純粋垂直境界の有限な添字型。
方針：補集合の純粋水平境界条件で制限する。
規約：KST A.5、大きい shuffle の水平数は p、垂直数は q+1。
使われ方：垂直境界の有限和の添字。 -/
abbrev VerticalShuffleBoundaryIndex (p q n : ℕ) (h : p + q = n) :=
  {z : ShuffleIndex p (n + 1) × Fin (n + 2) //
    IsHorizontalShuffleFace (z.1.transpose (show p + (q + 1) = n + 1 by omega)) z.2}

/-- 概要：二因子交換で水平境界と垂直境界の添字を同値にする。
方針：大きい shuffle を補集合で交換し、二回の交換で戻ることを使う。
規約：KST A.5、面の頂点番号は保つ。
使われ方：純粋垂直境界の全体への対応。 -/
def verticalBoundaryTransposeEquiv (p q n : ℕ) (h : p + q = n) :
    HorizontalShuffleBoundaryIndex q n ≃ VerticalShuffleBoundaryIndex p q n h where
  toFun z :=
    ⟨(z.val.1.transpose (show (q + 1) + p = n + 1 by omega), z.val.2), by
      simpa only [ShuffleIndex.transpose_transpose] using z.property⟩
  invFun z :=
    ⟨(z.val.1.transpose (show p + (q + 1) = n + 1 by omega), z.val.2), z.property⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · exact z.val.1.transpose_transpose (show (q + 1) + p = n + 1 by omega)
    · rfl
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · exact z.val.1.transpose_transpose (show p + (q + 1) = n + 1 by omega)
    · rfl

/-- 概要：小さい shuffle と第二因子の面番号は全ての純粋垂直境界に同値。
方針：小さい二因子交換、水平境界の同値、大きい二因子交換を合成する。
規約：KST Construction A.5、端点と内部の全ての面を含む。
使われ方：垂直境界和と通常境界和の添字の並べ替え。 -/
def verticalShuffleBoundaryEquiv (p q n : ℕ) (h : p + q = n) :
    (ShuffleIndex p n × Fin (q + 2)) ≃ VerticalShuffleBoundaryIndex p q n h :=
  (Equiv.prodCongr (shuffleTransposeEquiv p q n h) (Equiv.refl _)).trans
    ((horizontalShuffleBoundaryEquiv q n).trans (verticalBoundaryTransposeEquiv p q n h))

/-- 概要：垂直境界の同値の値は実際に指定面への垂直挿入と削除頂点。
方針：水平挿入と垂直挿入の二因子交換の公式を使う。
規約：KST A.5。使われ方：添字の同値へ実境界項の写像を対応させる。 -/
lemma verticalShuffleBoundaryEquiv_apply {p q n : ℕ} (h : p + q = n)
    (s : ShuffleIndex p n) (i : Fin (q + 2)) :
    (verticalShuffleBoundaryEquiv p q n h (s, i)).val =
      (s.insertVertical (s.verticalFacePosition h i), s.verticalFaceVertex h i) := by
  apply Prod.ext
  · change ((s.transpose h).insertHorizontal ((s.transpose h).horizontalFacePosition i)).transpose
      (show (q + 1) + p = n + 1 by omega) = s.insertVertical (s.verticalFacePosition h i)
    rw [← s.transpose_insertVertical h ((s.transpose h).horizontalFacePosition i),
      ShuffleIndex.transpose_transpose]
    rfl
  · rfl

/-- 概要：純粋垂直境界の和は小さい shuffle と第二因子の面の二重和へ移せる。
方針：補集合と挿入削除から構成した実同値に沿って有限和を移す。
規約：KST A.5、任意の可換加法モノイドの項に成立。
使われ方：shuffle の垂直境界和の比較。 -/
lemma verticalShuffleBoundary_sum {A : Type*} [AddCommMonoid A] (p q n : ℕ) (h : p + q = n)
    (F : VerticalShuffleBoundaryIndex p q n h → A) :
    ∑ z : VerticalShuffleBoundaryIndex p q n h, F z =
      ∑ s : ShuffleIndex p n, ∑ i : Fin (q + 2), F (verticalShuffleBoundaryEquiv p q n h (s, i)) := by
  have ht := Fintype.sum_equiv (verticalShuffleBoundaryEquiv p q n h)
    (fun z ↦ F (verticalShuffleBoundaryEquiv p q n h z)) F (fun _ ↦ rfl)
  simpa only [Fintype.sum_prod_type] using ht.symm

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
