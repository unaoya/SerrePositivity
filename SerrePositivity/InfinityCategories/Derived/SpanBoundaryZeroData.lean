module
public import SerrePositivity.InfinityCategories.Derived.SpanBoundaryAssembly

/-! # span 境界の零未知データ

概要：実際の境界の未知成分を零にした候補を作り、その全未知成分の零を確認する。
方針：組み立ての未知分岐に零の射族を渡す。
規約：HA Proposition 1.3.1.10。使われ方：D7 の残差の右辺と左右の共通面の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Opposite DifferentialGraded DGNerve
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：左セルの未知成分を全て零とした境界データ。
方針：左の組み立てデータに零の射族を指定する。
規約：全次元の dg nerve 境界。使われ方：左の右辺の既知残差の計算。 -/
def spanBoundaryLeftZeroData {n : ℕ}
    (F : join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ dgNerve A D) :
    SimplexData A D (n + 3) :=
  spanBoundaryLeftData F (fun _ _ _ _ _ _ _ _ => 0)

/-- 概要：左の零未知境界データは後続の全頂点を含む全ての成分で零。
方針：被覆面を選べないことから組み立ての未知分岐を評価する。
規約：先頭二頂点の所属は問わない。使われ方：未知残差を右辺の負へ変える。 -/
lemma spanBoundaryLeftZeroData_unknownHom {n : ℕ}
    (F : join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ dgNerve A D)
    (I : Finset (Fin (n + 4))) (hsuffix : spanSuffixFaces n ⊆ I)
    (a b : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    (spanBoundaryLeftZeroData F).hom I a b k hI ha hb hk = 0 := by
  have hn : ¬ ∃ j ∈ spanSuffixFaces n, j ∉ I := by
    rintro ⟨j, hj, hjI⟩
    exact hjI (hsuffix hj)
  simp only [spanBoundaryLeftZeroData, spanBoundaryLeftData, SelectedFaces.assembleData,
    dite_eq_right hn]

/-- 概要：右セルの未知成分を全て零とした境界データ。
方針：右の組み立てデータに零の射族を指定する。
規約：全次元の dg nerve 境界。使われ方：右の右辺の既知残差の計算。 -/
def spanBoundaryRightZeroData {n : ℕ}
    (F : join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ dgNerve A D) :
    SimplexData A D (n + 3) :=
  spanBoundaryRightData F (fun _ _ _ _ _ _ _ _ => 0)

/-- 概要：右の零未知境界データは後続の全頂点を含む全ての成分で零。
方針：被覆面を選べないことから組み立ての未知分岐を評価する。
規約：先頭二頂点の所属は問わない。使われ方：未知残差を右辺の負へ変える。 -/
lemma spanBoundaryRightZeroData_unknownHom {n : ℕ}
    (F : join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ dgNerve A D)
    (I : Finset (Fin (n + 4))) (hsuffix : spanSuffixFaces n ⊆ I)
    (a b : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    (spanBoundaryRightZeroData F).hom I a b k hI ha hb hk = 0 := by
  have hn : ¬ ∃ j ∈ spanSuffixFaces n, j ∉ I := by
    rintro ⟨j, hj, hjI⟩
    exact hjI (hsuffix hj)
  simp only [spanBoundaryRightZeroData, spanBoundaryRightData, SelectedFaces.assembleData,
    dite_eq_right hn]

end SerrePositivity.InfinityCategories
