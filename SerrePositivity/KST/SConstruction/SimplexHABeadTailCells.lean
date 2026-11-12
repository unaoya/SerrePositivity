module
public import SerrePositivity.KST.SConstruction.SimplexHABeadWordTransport
public import SerrePositivity.KST.SConstruction.SimplexSubsetLambdaInclusion

/-! # 未処理の右側頂点集合を持つ bead の実鎖射
概要：元の右側頂点集合と左端点から作った語の実鎖射を、元の部分集合生成射と同定。
方針：元の語の次元移送は元の cube 次元移送の前合成となり、端点移送を消去する。
規約：元の Λ Hom と Serre cube の実鎖射。使われ方：標準面への読み替えの基底。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の語の逆次元移送は、元の cube の同じ次元移送の実前合成。 -/
lemma simplexHABeadWordCell_mpr {n : ℕ} {a b : Fin (n + 1)} {p q : ℕ}
    (h : p = q) (word : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexHABeadWord n a b q) :
    simplexHABeadWordCell A (Eq.mpr (congrArg (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexHABeadWord n a b) h) word) =
      eqToHom (congrArg (serreCubeComplex A) h) ≫ simplexHABeadWordCell A word := by
  cases h
  exact (Category.id_comp _).symm

/-- 元の端点を指定した一 bead の語の実鎖射は、元の同じ部分集合生成射。 -/
lemma simplexHABeadWordAt_cell {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (a b : Fin (n + 1)) (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) :
    simplexHABeadWordCell A (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadWordAt I hI a b ha hb) =
      simplexSubsetLambdaCellAt A I a b hI ha hb := by
  subst a b
  rfl

/-- 元の右側頂点を持つ語の実鎖射は、元の次元移送と同じ部分集合生成射の合成。 -/
lemma simplexHABeadTail_cell {n : ℕ} (T : Finset (Fin (n + 1))) (hT : T.Nonempty)
    (a : Fin (n + 1)) (ha : ∀ t ∈ T, a < t) (hI : 2 ≤ (insert a T).card)
    (hmin : a = (insert a T).min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty _ hI))
    (hmax : T.max' hT = (insert a T).max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty _ hI)) :
    simplexHABeadWordCell A (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail T hT a ha) =
      eqToHom (congrArg (serreCubeComplex A)
        (show T.card - 1 = (insert a T).card - 2 by
          have hc := Finset.card_insert_of_notMem (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail_not_mem T a ha)
          omega)) ≫ simplexSubsetLambdaCellAt A (insert a T) a (T.max' hT) hI hmin hmax := by
  have hc := Finset.card_insert_of_notMem (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail_not_mem T a ha)
  have hd : T.card - 1 = (insert a T).card - 2 := by omega
  unfold _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail
  rw [simplexHABeadWordCell_mpr A hd, simplexHABeadWordAt_cell]

end SerrePositivity.KST.SConstruction
