module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SpanPresentations.SpanBoundaryAssembly

/-! # span 境界の零未知データ

概要：実際の境界の未知成分を零にした候補を作り、その全未知成分の零を確認する。
方針：組み立ての未知分岐に零の射族を渡す。
規約：HA Proposition 1.3.1.10。使われ方：D7 の残差の右辺と左右の共通面の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Opposite DifferentialGraded
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 概要：左セルの未知成分を全て零とした境界データ。
方針：左の組み立てデータに零の射族を指定する。
規約：全次元の dg nerve 境界。使われ方：左の右辺の既知残差の計算。 -/
def spanBoundaryLeftZeroData {n : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 3) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftData F (fun _ _ _ _ _ _ _ _ => 0)

/-- 概要：左の零未知境界データは後続の全頂点を含む全ての成分で零。
方針：被覆面を選べないことから組み立ての未知分岐を評価する。
規約：先頭二頂点の所属は問わない。使われ方：未知残差を右辺の負へ変える。 -/
lemma spanBoundaryLeftZeroData_unknownHom {n : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (I : Finset (Fin (n + 4))) (hsuffix : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n ⊆ I)
    (a b : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    (spanBoundaryLeftZeroData F).hom I a b k hI ha hb hk = 0 := by
  have hn : ¬ ∃ j ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n, j ∉ I := by
    rintro ⟨j, hj, hjI⟩
    exact hjI (hsuffix hj)
  simp only [spanBoundaryLeftZeroData, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftData, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceAssembly.assembleData,
    dite_eq_right hn]

/-- 概要：右セルの未知成分を全て零とした境界データ。
方針：右の組み立てデータに零の射族を指定する。
規約：全次元の dg nerve 境界。使われ方：右の右辺の既知残差の計算。 -/
def spanBoundaryRightZeroData {n : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 3) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightData F (fun _ _ _ _ _ _ _ _ => 0)

/-- 概要：右の零未知境界データは後続の全頂点を含む全ての成分で零。
方針：被覆面を選べないことから組み立ての未知分岐を評価する。
規約：先頭二頂点の所属は問わない。使われ方：未知残差を右辺の負へ変える。 -/
lemma spanBoundaryRightZeroData_unknownHom {n : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (I : Finset (Fin (n + 4))) (hsuffix : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n ⊆ I)
    (a b : Fin (n + 4)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    (spanBoundaryRightZeroData F).hom I a b k hI ha hb hk = 0 := by
  have hn : ¬ ∃ j ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n, j ∉ I := by
    rintro ⟨j, hj, hjI⟩
    exact hjI (hsuffix hj)
  simp only [spanBoundaryRightZeroData, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightData, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceAssembly.assembleData,
    dite_eq_right hn]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
